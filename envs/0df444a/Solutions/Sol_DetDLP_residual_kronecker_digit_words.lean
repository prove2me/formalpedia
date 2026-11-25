-- Prove2me | solution 1 for DetDLP.residual_kronecker_digit_words
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T13:53:51.237348+00:00
-- url     : https://prove2.me/submissions/50948c6c-8899-4dd9-a65b-4d20bd564732

import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

open Polynomial Finset


open DetDLP Finset
private theorem coeff_le_weight (p : Polynomial ℕ) (i : ℕ) : p.coeff i ≤ p.eval 1 := by
  classical
  rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
  simp only [one_pow,mul_one]
  by_cases hi : i ∈ p.support
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  · simp [Polynomial.notMem_support_iff.mp hi]

private theorem residual_no_wrap
    (G : BipartiteMultigraph) (digits h β : ℕ) (hedges : G.nE ≤ β)
    (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin digits → ℕ)
    (e : Fin digits → ℕ) (hA : ∀ v t j, A v t j < 2^h) :
    let Z : Polynomial ℕ := ∑ x : Fin G.nE → Bool, ∏ v : Fin G.nV,
      ∑ j : Fin digits, Polynomial.monomial (e j) (A v (fun i => x ((G.ports v).get i)) j)
    let P := β + G.nV*h + G.nV*Nat.clog 2 digits + 2
    ∀ i : ℕ, Z.coeff i < 2^P ∧ ((Z.coeff i : ZMod (2^P)).val) = Z.coeff i := by
  classical
  intro Z P i
  let V (v : Fin G.nV) (x : Fin G.nE → Bool) : Polynomial ℕ :=
    ∑ j : Fin digits, Polynomial.monomial (e j) (A v (fun k => x ((G.ports v).get k)) j)
  let W := digits*2^h
  have hw (v : Fin G.nV) (x : Fin G.nE → Bool) : (V v x).eval 1 ≤ W := by
    change Polynomial.evalRingHom 1 (∑ j : Fin digits, Polynomial.monomial (e j) _) ≤ _
    rw [map_sum]
    calc
      _ ≤ ∑ _ : Fin digits, 2^h := by
        apply Finset.sum_le_sum
        intro j _
        simpa [Polynomial.eval_monomial] using (hA v (fun k => x ((G.ports v).get k)) j).le
      _ = _ := by simp [W]
  have hweight : Z.eval 1 ≤ 2^G.nE * W^G.nV := by
    change Polynomial.evalRingHom 1 (∑ x : Fin G.nE → Bool, ∏ v, V v x) ≤ _
    rw [map_sum]
    calc
      _ ≤ ∑ x : Fin G.nE → Bool, ∏ _ : Fin G.nV, W := by
        apply Finset.sum_le_sum
        intro x _
        rw [map_prod]
        exact Finset.prod_le_prod' (fun v _ => hw v x)
      _ = _ := by simp [Fintype.card_fun]
  have hdig := Nat.le_pow_clog (by decide : 1 < 2) digits
  have hu : W ≤ 2^(Nat.clog 2 digits+h) := by
    rw [pow_add]; exact Nat.mul_le_mul_right _ hdig
  have huv : 2^G.nE*W^G.nV ≤ 2^(β+G.nV*h+G.nV*Nat.clog 2 digits) := by
    calc
      _ ≤ 2^β * (2^(Nat.clog 2 digits+h))^G.nV :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hedges) (Nat.pow_le_pow_left hu _)
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; ring
  have hv : Z.coeff i < 2^P := by
    apply lt_of_le_of_lt ((coeff_le_weight Z i).trans (hweight.trans huv))
    exact Nat.pow_lt_pow_right (by decide) (by dsimp [P]; omega)
  exact ⟨hv,ZMod.val_natCast_of_lt hv⟩

namespace DetDLP.TerminalKronecker
open Polynomial Finset
open scoped Polynomial

variable {R : Type*} [CommRing R]

noncomputable def pack (K : ℕ) : Polynomial (Polynomial R) →+* Polynomial R :=
  Polynomial.eval₂RingHom (RingHom.id _) (X^K)

def Width (P : Polynomial (Polynomial R)) (d : ℕ) : Prop :=
  ∀ j, (P.coeff j).natDegree ≤ d

theorem recover (P : Polynomial (Polynomial R)) (d K i j : ℕ) (hd : Width P d)
    (hK : d < K) (hi : i < K) : (pack K P).coeff (i+K*j) = (P.coeff j).coeff i := by
  classical
  let n := max P.natDegree j + 1
  change (P.eval₂ (RingHom.id _) (X^K)).coeff _ = _
  rw [eval₂_eq_sum_range' _ (show P.natDegree < n by dsimp [n]; omega),finsetSum_coeff]
  simp only [RingHom.id_apply,← pow_mul]
  rw [Finset.sum_eq_single j]
  · exact coeff_mul_X_pow _ _ _
  · intro t _ ht
    rw [coeff_mul_X_pow']
    rcases lt_or_gt_of_ne ht with h|h
    · have e : K*t+K ≤ K*j := by simpa only [Nat.mul_succ] using Nat.mul_le_mul_left K (show t+1 ≤ j by omega)
      rw [if_pos (by omega)]; apply coeff_eq_zero_of_natDegree_lt
      have := hd t; omega
    · have e : K*j+K ≤ K*t := by simpa only [Nat.mul_succ] using Nat.mul_le_mul_left K (show j+1 ≤ t by omega)
      rw [if_neg (by omega)]
  · intro hn; exact (hn (Finset.mem_range.mpr (by dsimp [n]; omega))).elim

theorem width_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Polynomial R)) (d : ℕ)
    (hf : ∀ i∈s,Width (f i) d) : Width (∑ i∈s,f i) d := by
  intro j; rw [finsetSum_coeff]
  exact natDegree_sum_le_of_forall_le _ _ (fun i hi => hf i hi j)

theorem width_mul {P Q : Polynomial (Polynomial R)} {d e : ℕ}
    (hp : Width P d) (hq : Width Q e) : Width (P*Q) (d+e) := by
  intro j; rw [coeff_mul]
  apply natDegree_sum_le_of_forall_le
  exact fun x _ => natDegree_mul_le.trans (Nat.add_le_add (hp x.1) (hq x.2))

theorem width_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Polynomial R))
    (d : ℕ) (hf : ∀ i∈s,Width (f i) d) : Width (∏ i∈s,f i) (s.card*d) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro j; simp [coeff_one]; split <;> simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.card_insert_of_notMem ha,Nat.succ_mul,add_comm]
    apply width_mul (hf a (by simp))
    exact ih (fun i hi => hf i (by simp [hi]))

theorem contract_width (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Polynomial (Polynomial R))
    (d : ℕ) (hT : ∀ v t,Width (T v t) d) : Width (BTNContract G T) (G.nV*d) := by
  apply width_sum
  intro x _
  simpa using width_prod (Finset.univ : Finset (Fin G.nV))
    (fun v => T v (fun i => x ((G.ports v).get i))) d (fun v _ => hT v _)

theorem pack_contract (G : BipartiteMultigraph) (K : ℕ)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Polynomial (Polynomial R)) :
    pack K (BTNContract G T) = BTNContract G (fun v t => pack K (T v t)) := by
  classical
  simp [BTNContract]

theorem digit_expansion (G : BipartiteMultigraph) (J : ℕ)
    (w : Fin J → R)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin J → Polynomial (Polynomial R)) :
    BTNContract G (fun v t => ∑ a, C (C (w a))*T v t a) =
      ∑ a : Fin G.nV → Fin J, C (C (∏ v, w (a v))) *
        BTNContract G (fun v t => T v t (a v)) := by
  classical
  unfold BTNContract
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib,map_prod,map_prod]

theorem coefficients (G : BipartiteMultigraph) (J d i j : ℕ)
    (w : Fin J → R)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin J → Polynomial (Polynomial R))
    (ht : ∀ v t a,Width (T v t a) d) (hi : i < G.nV*d+1) :
    let K := G.nV*d+1
    ((BTNContract G (fun v t => ∑ a, C (C (w a))*T v t a)).coeff j).coeff i =
      ∑ a : Fin G.nV → Fin J, (∏ v,w (a v)) *
        (BTNContract G (fun v t => pack K (T v t (a v)))).coeff (i+K*j) := by
  intro K
  rw [digit_expansion,finsetSum_coeff,finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro a _
  rw [coeff_C_mul,coeff_C_mul,← pack_contract]
  congr 1
  exact (recover _ _ _ _ _ (contract_width G _ d (fun v t => ht v t (a v))) (Nat.lt_succ_self _) hi).symm

end DetDLP.TerminalKronecker

namespace DetDLP.TerminalDigitRecovery
open TerminalKronecker Polynomial Finset
open scoped Polynomial

def grid {κ ℓ : ℕ} (i : Fin (κ*ℓ)) := (finProdFinEquiv (m:=κ) (n:=ℓ)).symm i
def exponent {κ ℓ : ℕ} (K : ℕ) (i : Fin (κ*ℓ)) := (grid i).1.val+K*(grid i).2.val

noncomputable def entry {κ ℓ : ℕ} (a : Fin (κ*ℓ) → ℕ) : Polynomial (Polynomial ℤ) :=
  ∑ i, monomial (grid i).2.val (monomial (grid i).1.val ((a i):ℤ))

theorem width_entry {κ ℓ : ℕ} (a : Fin (κ*ℓ) → ℕ) : Width (entry a) (κ-1) := by
  apply width_sum
  intro s _ j
  rw [coeff_monomial]
  split
  · exact (natDegree_monomial_le _).trans (by have := (grid s).1.isLt; omega)
  · simp

theorem pack_entry {κ ℓ : ℕ} (K : ℕ) (a : Fin (κ*ℓ) → ℕ) :
    pack K (entry a) = ∑ i, monomial (exponent K i) ((a i):ℤ) := by
  classical
  unfold entry
  rw [map_sum]; apply sum_congr rfl
  intro i _
  change eval₂ (RingHom.id _) (X^K) (monomial _ _) = _
  simp [eval₂_monomial,← pow_mul,exponent,← C_mul_X_pow_eq_monomial,← mul_assoc,← pow_add,mul_assoc]

theorem exact_packed (G : BipartiteMultigraph) (κ ℓ h β K : ℕ) (he : G.nE ≤ β)
    (a : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin (κ*ℓ) → ℕ)
    (ha : ∀ v t s, a v t s < 2^h) (i : ℕ) :
    let P := β+G.nV*h+G.nV*Nat.clog 2 (κ*ℓ)+2
    let modEntry (v : Fin G.nV) (t : Fin (G.deg v) → Bool) : Polynomial (ZMod (2^P)) :=
      ∑ s, monomial (exponent K s) ((a v t s):ZMod (2^P))
    (BTNContract G (fun v t => pack K (entry (a v t)))).coeff i =
      (((BTNContract G modEntry).coeff i).val:ℤ) := by
  classical
  intro P modEntry
  let Z : Polynomial ℕ := ∑ x : Fin G.nE → Bool, ∏ v : Fin G.nV,
    ∑ s, monomial (exponent K s) (a v (fun u => x ((G.ports v).get u)) s)
  have hval := (residual_no_wrap G (κ*ℓ) h β he a (exponent K) ha i).2
  change ((Z.coeff i:ZMod (2^P)).val) = Z.coeff i at hval
  have comp (R : Type) [CommRing R] : Z.map (Nat.castRingHom R) =
      BTNContract G (fun v t => ∑ s, monomial (exponent K s) ((a v t s):R)) := by
    simp [Z,BTNContract,Polynomial.map_sum,Polynomial.map_prod]
  simp only [pack_entry]
  change (BTNContract G (fun v t => ∑ s, monomial (exponent K s) ((a v t s):ℤ))).coeff i =
      (((BTNContract G (fun v t => ∑ s, monomial (exponent K s) ((a v t s):ZMod (2^P)))).coeff i).val:ℤ)
  rw [← comp ℤ,← comp (ZMod (2^P)),coeff_map,coeff_map]
  exact congrArg (fun n : ℕ => (n:ℤ)) hval.symm

theorem digit_recovery (G : BipartiteMultigraph) (κ ℓ J h β i j : ℕ) (he : G.nE ≤ β)
    (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin J → Fin (κ*ℓ) → ℕ)
    (hA : ∀ v t a s,A v t a s < 2^h) (hi : i < G.nV*(κ-1)+1) :
    let K := G.nV*(κ-1)+1
    let P := β+G.nV*h+G.nV*Nat.clog 2 (κ*ℓ)+2
    let full (v : Fin G.nV) (t : Fin (G.deg v) → Bool) :=
      ∑ a : Fin J,C (C ((2:ℤ)^(h*a.val))) * entry (A v t a)
    let slice (a : Fin G.nV → Fin J) (v : Fin G.nV) (t : Fin (G.deg v) → Bool) : Polynomial (ZMod (2^P)) :=
      ∑ s, monomial (exponent K s) ((A v t (a v) s):ZMod (2^P))
    ((BTNContract G full).coeff j).coeff i = ∑ a : Fin G.nV → Fin J,
      (2:ℤ)^(h*∑ v,(a v).val) * (((BTNContract G (slice a)).coeff (i+K*j)).val:ℤ) := by
  classical
  intro K P full slice
  rw [show full = _ from rfl,coefficients G J (κ-1) i j (fun a => (2:ℤ)^(h*a.val))
    (fun v t a => entry (A v t a)) (fun v t a => width_entry _) hi]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.prod_pow_eq_pow_sum,← Finset.mul_sum]
  rw [exact_packed G κ ℓ h β K he (fun v t => A v t (a v)) (fun v t s => hA v t _ s)]

end DetDLP.TerminalDigitRecovery

namespace DetDLP.TerminalDigitWords
open TerminalDigitRecovery Polynomial Finset
open scoped Polynomial

def limb (h a x : ℕ) := x / 2^(h*a) % 2^h

theorem digit_sum (h J x : ℕ) (hx : x < 2^(h*J)) :
    ∑ a : Fin J, 2^(h*a.val)*limb h a.val x = x := by
  have eq (j : ℕ) : ∑ a : Fin j, (2^h)^a.val*(x/(2^h)^a.val%(2^h)) = x%(2^h)^j := by
    induction j with
    | zero => simp [Nat.mod_one]
    | succ n ih => rw [Fin.sum_univ_castSucc]; simpa [Nat.mod_pow_succ,ih]
  simpa only [limb,← pow_mul,Nat.mod_eq_of_lt hx] using eq J

theorem entry_sum {κ ℓ : ℕ} (h J : ℕ) (A : Fin (κ*ℓ) → ℕ) (ha : ∀ s,A s < 2^(h*J)) :
    entry A = ∑ a : Fin J, C (C ((2:ℤ)^(h*a.val))) * entry (fun s => limb h a.val (A s)) := by
  classical
  unfold entry
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  simp only [C_mul_monomial]
  rw [← map_sum,← map_sum]
  congr 2
  exact_mod_cast (digit_sum h J (A s) (ha s)).symm

theorem output_coeff (P L : ℕ) (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Polynomial (ZMod (2^P)))
    (w : List Bool) (hw : EncodesTruncPoly P L w (BTNContract G (fun v t => Ideal.Quotient.mk _ (T v t)))) :
    w = encodeNatListBin (List.ofFn fun i : Fin L => ((BTNContract G T).coeff i.val).val) := by
  classical
  obtain ⟨c,hc,rfl,he⟩ := hw
  have ec : Ideal.Quotient.mk (Ideal.span {((X:Polynomial (ZMod (2^P)))^L)}) (BTNContract G T) =
      Ideal.Quotient.mk _ (∑ i : Fin L, monomial i.val ((c i):ZMod (2^P))) := by
    simpa [BTNContract,truncPolyOfCoeffs] using he
  have ew := Ideal.Quotient.eq.mp ec
  rw [Ideal.mem_span_singleton,Polynomial.X_pow_dvd_iff] at ew
  congr 1; congr 1; funext i
  have ei := ew i.val i.isLt
  rw [coeff_sub,sub_eq_zero,finsetSum_coeff] at ei
  have Es : (∑ s : Fin L,(monomial s.val ((c s):ZMod (2^P))).coeff i.val) = (c i:ZMod (2^P)) := by
    rw [Finset.sum_eq_single i]
    · simp [coeff_monomial]
    · intro b _ hb; simp [coeff_monomial,show b.val ≠ i.val from fun e => hb (Fin.ext e),show i.val ≠ b.val from fun e => hb (Fin.ext e.symm)]
    · simp
  rw [Es] at ei
  simpa only [ei,ZMod.val_natCast_of_lt (hc i)]

theorem residual_words (G : BipartiteMultigraph) (κ ℓ J h β : ℕ) (he : G.nE ≤ β)
    (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin (κ*ℓ) → ℕ)
    (hA : ∀ v t s,A v t s < 2^(h*J)) :
    let K := G.nV*(κ-1)+1
    let P := β+G.nV*h+G.nV*Nat.clog 2 (κ*ℓ)+2
    let L := K*ℓ
    let slice (a : Fin G.nV → Fin J) (v : Fin G.nV) (t : Fin (G.deg v) → Bool) : Polynomial (ZMod (2^P)) :=
      ∑ s, monomial (exponent K s) ((limb h (a v).val (A v t s)):ZMod (2^P))
    ∀ w : (Fin G.nV → Fin J) → List Bool,
      (∀ a,EncodesTruncPoly P L (w a) (BTNContract G (fun v t => Ideal.Quotient.mk _ (slice a v t)))) →
      ∃ c : (Fin G.nV → Fin J) → Fin L → ℕ,
        (∀ a,w a=encodeNatListBin (List.ofFn (c a))) ∧ (∀ a i,c a i < 2^P) ∧
        ∀ i : Fin K, ∀ j : Fin ℓ,
          ((BTNContract G (fun v t => entry (A v t))).coeff j.val).coeff i.val =
            ∑ a : Fin G.nV → Fin J, (2:ℤ)^(h*∑ v,(a v).val) *
              ((c a ⟨i.val+K*j.val,by
                have H := Nat.mul_le_mul_left K j.isLt
                rw [Nat.mul_succ] at H; have := i.isLt; omega⟩):ℤ) := by
  classical
  intro K P L slice w hw
  let c (a : Fin G.nV → Fin J) (i : Fin L) := ((BTNContract G (slice a)).coeff i.val).val
  refine ⟨c,fun a => output_coeff _ _ G _ _ (hw a),fun a i => ZMod.val_lt _,?_⟩
  intro i j
  have heq (v : Fin G.nV) (t : Fin (G.deg v) → Bool) := entry_sum h J (A v t) (hA v t)
  simp_rw [heq]
  exact digit_recovery G κ ℓ J h β i.val j.val he (fun v t a s => limb h a.val (A v t s))
    (fun _ _ _ _ => Nat.mod_lt _ (by positivity)) i.isLt

end DetDLP.TerminalDigitWords
open DetDLP

theorem solution (G : BipartiteMultigraph) (κ ℓ J h β : ℕ) (he : G.nE ≤ β)
    (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin (κ*ℓ) → ℕ)
    (hA : ∀ v t s,A v t s < 2^(h*J)) :
    let K := G.nV*(κ-1)+1
    let P := β+G.nV*h+G.nV*Nat.clog 2 (κ*ℓ)+2
    let L := K*ℓ
    let coord := (finProdFinEquiv (m:=κ) (n:=ℓ)).symm
    let full (v : Fin G.nV) (t : Fin (G.deg v) → Bool) : Polynomial (Polynomial ℤ) :=
      ∑ s, monomial (coord s).2.val (monomial (coord s).1.val ((A v t s):ℤ))
    let slice (a : Fin G.nV → Fin J) (v : Fin G.nV) (t : Fin (G.deg v) → Bool) : Polynomial (ZMod (2^P)) :=
      ∑ s, monomial ((coord s).1.val+K*(coord s).2.val)
        (((A v t s / 2^(h*(a v).val) % 2^h):ℕ):ZMod (2^P))
    ∀ w : (Fin G.nV → Fin J) → List Bool,
      (∀ a,EncodesTruncPoly P L (w a) (BTNContract G (fun v t => Ideal.Quotient.mk _ (slice a v t)))) →
      ∃ c : (Fin G.nV → Fin J) → Fin L → ℕ,
        (∀ a,w a=encodeNatListBin (List.ofFn (c a))) ∧ (∀ a i,c a i < 2^P) ∧
        ∀ i : Fin K, ∀ j : Fin ℓ,
          ((BTNContract G full).coeff j.val).coeff i.val =
            ∑ a : Fin G.nV → Fin J, (2:ℤ)^(h*∑ v,(a v).val) *
              ((c a ⟨i.val+K*j.val,by
                have H := Nat.mul_le_mul_left K j.isLt
                rw [Nat.mul_succ] at H; have := i.isLt; omega⟩):ℤ) := by
  exact TerminalDigitWords.residual_words G κ ℓ J h β he A hA
