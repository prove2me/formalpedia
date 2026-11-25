-- Prove2me | solution 1 for DetDLP.fp_dlp_machine_computes_bezout_residue
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T01:42:50.589716+00:00
-- url     : https://prove2.me/submissions/7631b001-eb8d-4d86-954f-c2ceb2bb3bd9

import Definitions.Def_DetDLP_W1_Queries
import Definitions.Def_DetDLP_W1_Bounds
set_option autoImplicit false
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
namespace DetDLP_W1_Final
open DetDLP_W1_Bounds DetDLP_W1_Queries
noncomputable section

def Good {p : ℕ} (g t : (ZMod p)ˣ) : Option ℕ → Prop
  | none => t ∉ Subgroup.zpowers g
  | some x => x < orderOf g ∧ g ^ x = t

theorem correct {p : ℕ} [Fact p.Prime] (h g t : (ZMod p)ˣ) (u v : ℕ) (hh : orderOf h = p-1) (hu : u < p-1) (hgu : h^u = g) (htv : h^v = t) : Good g t (DetDLP_W1_Euclid.answer (p-1) u v) := by
  let n := p - 1
  let d := Nat.gcd u n
  let z : ℤ := Nat.gcdA u n * ((v / d : ℕ) : ℤ)
  let x := (z % (((n/d : ℕ) : ℤ))).toNat
  have horder : orderOf g = n/d := by
    rw [← hgu, orderOf_pow, hh, Nat.gcd_comm]
  have hpos : 0 < (↑(n/d) : ℤ) := by exact_mod_cast horder ▸ orderOf_pos g
  have hxcast : (x : ℤ) = z % ((n/d : ℕ) : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hpos))
  have hbound : x < orderOf g := by
    rw [horder]
    exact_mod_cast (show (x : ℤ) < ((n/d : ℕ) : ℤ) by rw [hxcast]; exact Int.emod_lt_of_pos _ hpos)
  have hpower (hd : d ∣ v) : g ^ x = t := by
    have hmul : (d : ℤ) * ((v/d : ℕ) : ℤ) = (v : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' hd
    have hmod : (u : ℤ) * z ≡ (v : ℤ) [ZMOD (orderOf h : ℤ)] := by
      rw [hh]
      change (u : ℤ) * (Nat.gcdA u n * _) ≡ (v : ℤ) [ZMOD (n : ℤ)]
      rw [← mul_assoc, ← hmul]
      exact (Int.gcd_a_modEq u n).mul_right _
    calc
      g ^ x = g ^ (z % (orderOf g : ℤ)) := by rw [← zpow_natCast, hxcast, horder]
      _ = g ^ z := zpow_mod_orderOf _ _
      _ = h ^ ((u : ℤ) * z) := by rw [zpow_mul h (u : ℤ) z, zpow_natCast, hgu]
      _ = h ^ (v : ℤ) := zpow_eq_zpow_iff_modEq.mpr hmod
      _ = t := by rw [zpow_natCast, htv]
  have hnecess (ht : t ∈ Subgroup.zpowers g) : d ∣ v := by
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp ht)
    have hmod : u * k ≡ v [MOD n] := by
      change u * k ≡ v [MOD p - 1]
      rw [← hh, ← pow_eq_pow_iff_modEq (x := h), pow_mul, hgu, hk, htv]
    exact (hmod.dvd_iff (Nat.gcd_dvd_right u n)).mp
      ((Nat.gcd_dvd_left u n).trans (dvd_mul_right u k))
  rw [DetDLP_W1_Euclid.answer_spec (by omega : 0 < p-1) hu.le]
  change Good g t (if d ∣ v then some x else none)
  split_ifs with hd
  · exact ⟨hbound,hpower hd⟩
  · exact fun ht => hd (hnecess ht)

theorem unique {p : ℕ} [Fact p.Prime] {g t : (ZMod p)ˣ} {a b : Option ℕ} (ha : Good g t a) (hb : Good g t b) : a=b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some y => exact False.elim (ha (hb.2 ▸ (Subgroup.zpowers g).pow_mem (Subgroup.mem_zpowers g) y))
  | some x => cases b with
    | none => exact False.elim (hb (ha.2 ▸ (Subgroup.zpowers g).pow_mem (Subgroup.mem_zpowers g) x))
    | some y => exact congrArg some (pow_injOn_Iio_orderOf (x:=g) ha.1 hb.1 (ha.2.trans hb.2.symm))

structure Instance where
  p : ℕ
  prime : Fact p.Prime
  g : (ZMod p)ˣ
  t : (ZMod p)ˣ
attribute [instance] Instance.prime

def S (i : Instance) := sScale (bitLen i.p)
def T (i : Instance) := 4*tScale (bitLen i.p)
theorem hS (i : Instance) : 1 ≤ S i := scales_one (Nat.clog_pos (by decide) i.prime.out.one_lt)
theorem hST (i : Instance) : S i ≤ T i := compareScale _
theorem sDom (k : ℕ) : Dom S (fun i => mainSpaceBound k (bitLen i.p)) := ⟨k,fun i => (sEq _ _).ge⟩
theorem tDom (k : ℕ) : Dom T (fun i => mainTimeBound k (bitLen i.p)) := by
  refine ⟨k,fun i => ?_⟩; change mainTimeBound k _ ≤ _; rw [← tEq]; apply Real.rpow_le_rpow_of_exponent_le (by norm_num); apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _); change tScale _ ≤ 4*tScale _; have hh := (hS i).trans (hST i); unfold T at hh; linarith

def w0 (i : Instance) := encodeFpDLPInput i.p i.g.val.val i.t.val.val
private theorem len_mono {p a : ℕ} (hp : 0 < p) (ha : a ≤ p) : (countWord a).length ≤ (countWord p).length := by
  unfold countWord; rw [if_neg hp.ne']; split_ifs with hz
  · change 1 ≤ p.bits.length; rw [Nat.size_eq_bits_len]; have := Nat.lt_size_self p; by_contra! h; rw [show p.size = 0 by omega] at this; simp at this; omega
  · simpa only [← Nat.size_eq_bits_len] using Nat.size_le_size ha
private theorem frameLen (x : List Bool) : (Encoding.frame x).length = 2*x.length+1 := by
  induction x with
  | nil => rfl
  | cons b x ih => change (Encoding.frame x).length+1+1 = 2*(x.length+1)+1; omega

theorem short_input (hp : Short S (fun i => countWord i.p)) : Short S w0 := by
  apply (Dom.add hS ((dconst hS 6).mul hp (fun _ => by norm_num) (fun _ => by positivity)) (dconst hS 7)).weaken
  intro i; have hg := len_mono i.prime.out.pos (ZMod.val_lt i.g.val).le; have ht := len_mono i.prime.out.pos (ZMod.val_lt i.t.val).le
  simp [w0,encodeFpDLPInput,encodeNatListBin,Encoding.encodeList,frameLen]; exact_mod_cast (by omega : 2*(countWord i.p).length+1+(2*(countWord i.g.val.val).length+1+(2*(countWord i.t.val.val).length+1+1+1)+1)+1 ≤ 6*(countWord i.p).length+7)

private theorem input_le_budget {M : PrimitiveMachine} {o : Fin M.tapeCount} {x y : List Bool} {τ σ : ℝ} (h : RunsWithin M o x y τ σ) : (x.length : ℝ) ≤ σ := by
  obtain ⟨n,c,tr,hh,ho,hn,hs⟩ := h
  have hv := hs 0 _ (Nat.zero_le _) (.refl _)
  apply le_trans _ hv
  exact_mod_cast (show x.length ≤ visitedSpace (locatedInit M x) by
    unfold visitedSpace
    apply le_trans _ (Finset.single_le_sum (f := fun i => ((locatedInit M x).upper i - (locatedInit M x).lower i + 1).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ M.inputTape))
    simp [locatedInit]; omega)

end
end DetDLP_W1_Final

open DetDLP_W1_Final DetDLP_W1_Bounds DetDLP_W1_Queries
theorem solution :
    (∃ (M_pr : PrimitiveMachine) (out_pr : Fin M_pr.tapeCount) (C_pr : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ h : (ZMod p)ˣ,
          orderOf h = p - 1 ∧
          RunsWithin M_pr out_pr (countWord p) (countWord (h : ZMod p).val)
            (mainSpaceBound C_pr (bitLen p)) (mainSpaceBound C_pr (bitLen p))) →
    (∃ (M_full : PrimitiveMachine) (out_full : Fin M_full.tapeCount) (C_full : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (h a : (ZMod p)ˣ),
        orderOf h = p - 1 →
        ∃ u : ℕ, u < p - 1 ∧ h ^ u = a ∧
          RunsWithin M_full out_full (encodeFpDLPInput p (h : ZMod p).val (a : ZMod p).val)
            (countWord u)
            (mainTimeBound C_full (bitLen p)) (mainSpaceBound C_full (bitLen p))) →
    (∃ (M_fp : PrimitiveMachine) (out_fp : Fin M_fp.tapeCount) (C_fp : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (h g t : (ZMod p)ˣ) (u v : ℕ),
        orderOf h = p - 1 → u < p - 1 → v < p - 1 → h ^ u = g → h ^ v = t →
        let n := p - 1
        let d := Nat.gcd u n
        let x := ((Nat.gcdA u n * (v / d : ℕ)) % ((n / d : ℕ) : ℤ)).toNat
        RunsWithin M_fp out_fp (encodeFpDLPInput p (g : ZMod p).val (t : ZMod p).val)
          (encodeOptionNatBin (if d ∣ v then some x else none))
          (mainTimeBound C_fp (bitLen p)) (mainSpaceBound C_fp (bitLen p))) := by
  classical
  rintro ⟨P,po,cp,hP⟩ ⟨F,fo,cf,hF⟩
  choose h hh hr using fun (i : Instance) => hP i.p
  choose u hu hgu ur using fun (i : Instance) => hF i.p (h i) i.g (hh i)
  choose v hv htv vr using fun (i : Instance) => hF i.p (h i) i.t (hh i)
  let wh := fun i => countWord (h i).val.val
  let wu := fun i => countWord (u i)
  let wv := fun i => countWord (v i)
  let a := fun i => saved (w0 i) (wh i)
  let b := fun i => saved (a i) (wu i)
  let c := fun i => saved (b i) (wv i)
  have hp : Short S (fun i => countWord i.p) := (sDom cp).weaken (fun i => input_le_budget (hr i))
  have shortNum (f : Instance → ℕ) (hf : ∀ i, f i ≤ i.p) : Short S (fun i => countWord (f i)) :=
    Dom.weaken hp (fun i => by exact_mod_cast len_mono i.prime.out.pos (hf i))
  have sh := shortNum (fun i => (h i).val.val) (fun i => (ZMod.val_lt _).le)
  have su := shortNum u (fun i => by have := hu i; omega)
  have sv := shortNum v (fun i => by have := hv i; omega)
  have s0 := short_input hp
  have sa := shortPack hS s0 sh
  have sb := shortPack hS sa su
  have sc := shortPack hS sb sv
  have f1 : Family S T (fun i => q1 (w0 i)) wh := ⟨P,po,_,_,liftTime hS hST (sDom cp),sDom cp,fun i => by simpa [w0,wh] using hr i⟩
  have f2 : Family S T (fun i => q2 (a i)) wu := ⟨F,fo,_,_,tDom cf,sDom cf,fun i => by simpa [a,w0,wh,wu] using ur i⟩
  have f3 : Family S T (fun i => q3 (b i)) wv := ⟨F,fo,_,_,tDom cf,sDom cf,fun i => by simpa [b,a,w0,wh,wu,wv] using vr i⟩
  have ha : Family S T w0 a := save hS hST s0 sh (seq hS hST (poly hS hST s0 q1 pq1) f1)
  have hb : Family S T a b := save hS hST sa su (seq hS hST (poly hS hST sa q2 pq2) f2)
  have hc : Family S T b c := save hS hST sb sv (seq hS hST (poly hS hST sb q3 pq3) f3)
  obtain ⟨M,o,τ,σ,⟨kt,ht⟩,⟨ks,hs⟩,hrun⟩ := seq hS hST ha (seq hS hST hb (seq hS hST hc (poly hS hST sc q4 pq4)))
  refine ⟨M,o,max (4*kt) ks,?_⟩
  intro p hp' h' g t u' v' hh' hu' _ hgu' htv'
  let i : Instance := ⟨p,hp',g,t⟩
  have hc' := correct (h i) i.g i.t (u i) (v i) (hh i) (hu i) (hgu i) (htv i)
  have he := unique (g:=g) (t:=t) hc' (correct h' g t u' v' hh' hu' hgu' htv')
  have out := hrun i
  change RunsWithin M o (w0 i) (q4 (saved (saved (saved (encodeFpDLPInput i.p i.g.val.val i.t.val.val) (countWord (h i).val.val)) (countWord (u i))) (countWord (v i)))) (τ i) (σ i) at out
  rw [q4_spec,he,DetDLP_W1_Euclid.answer_spec (by omega : 0 < p-1) hu'.le] at out
  apply MachineComposition.runsWithin_mono out
  · apply (ht i).trans
    have htpos : 0 ≤ tScale (bitLen p) := by unfold tScale; positivity
    change E (4*tScale (bitLen p)) kt ≤ mainTimeBound (max (4*kt) ks) (bitLen p)
    calc
      E (4*tScale (bitLen p)) kt = mainTimeBound (4*kt) (bitLen p) := by rw [← tEq]; unfold E; push_cast; ring_nf
      _ ≤ mainTimeBound (max (4*kt) ks) (bitLen p) := by
        calc
          mainTimeBound (4*kt) (bitLen p) = E (tScale (bitLen p)) (4*kt) := (tEq _ _).symm
          _ ≤ E (tScale (bitLen p)) (max (4*kt) ks) := monoE (by positivity) (le_max_left _ _)
          _ = mainTimeBound (max (4*kt) ks) (bitLen p) := tEq _ _
  · apply (hs i).trans; rw [← sEq]; apply monoE (le_trans zero_le_one (hS i)); exact le_max_right _ _
