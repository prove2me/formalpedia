-- Prove2me | solution 2 for DeletionHash.MixedEdit.substring_edit_codes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:05:22.984417+00:00
-- url     : https://prove2.me/submissions/72d0e0aa-57fa-4616-ac7a-73de10945f59

import Mathlib
import Definitions.Def_DeletionHash_MixedEdit_ConflictGraph
import Theorems.Thm_DeletionHash_MixedEdit_most_words_unique
import Theorems.Thm_DeletionHash_MixedEdit_nonseparated_thin
import Theorems.Thm_DeletionHash_MixedEdit_odd_cycles_rare


/-!
The deterministic selection at the end of the manuscript. The vertices in
bipartite connected components admit a coherent two-coloring, constructed
by choosing a coloring for each component. One global color class contains
at least half those vertices and is independent. A separate finite-fiber
argument retains at least a 1/Q fraction in one label class.
-/
namespace DeletionGraph.BipartiteSelection

open SimpleGraph
open scoped BigOperators

/-- The finite pigeonhole bound in multiplication form, without rounding.
The selected label exists even when I is empty. -/
theorem exists_large_label_fiber {V : Type*} {Q : ℕ} (I : Finset V)
    (label : V → Fin Q) (hQ : 1 ≤ Q) :
    ∃ a : Fin Q, I.card ≤ Q * (I.filter (fun v => label v = a)).card := by
  classical
  have hne : (Finset.univ : Finset (Fin Q)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin Q))
    (fun b => (I.filter (fun v => label v = b)).card) hne
  refine ⟨a, ?_⟩
  calc
    I.card = ∑ b : Fin Q, (I.filter (fun v => label v = b)).card := by
      symm
      simpa only [Finset.mem_univ, Finset.filter_true] using
        Finset.sum_card_fiberwise_eq_card_filter I (Finset.univ : Finset (Fin Q)) label
    _ ≤ ∑ _b : Fin Q, (I.filter (fun v => label v = a)).card :=
      Finset.sum_le_sum (fun b hb => ha b hb)
    _ = _ := by simp

variable {V : Type*} (G : SimpleGraph V)

/-- A vertex is retained at this stage exactly when its whole component is bipartite. -/
def Good (v : V) : Prop := (G.connectedComponentMk v).toSimpleGraph.Colorable 2

/-- Choose one coloring per bipartite component. The fallback value on other
components is unused by the independent-set construction. -/
noncomputable def componentColor (C : G.ConnectedComponent) : C → Fin 2 := by
  classical
  exact if h : C.toSimpleGraph.Colorable 2 then fun v => h.some v else fun _ => 0

theorem componentColor_valid (C : G.ConnectedComponent) (hC : C.toSimpleGraph.Colorable 2)
    {v w : C} (hvw : C.toSimpleGraph.Adj v w) :
    componentColor G C v ≠ componentColor G C w := by
  classical
  simpa only [componentColor, dif_pos hC] using hC.some.valid hvw

/-- The same component choice is used at every vertex in that component. -/
noncomputable def color (v : V) : Fin 2 :=
  componentColor G (G.connectedComponentMk v) ⟨v, rfl⟩

theorem color_eq_component (C : G.ConnectedComponent) (v : V) (hv : v ∈ C) :
    color G v = componentColor G C ⟨v, hv⟩ := by
  change G.connectedComponentMk v = C at hv
  subst C
  rfl

/-- Adjacent retained vertices receive different colors; no coloring of
the nonbipartite components is assumed. -/
theorem good_color_valid {v w : V} (hv : Good G v) (hvw : G.Adj v w) :
    color G v ≠ color G w := by
  let C := G.connectedComponentMk v
  have hvC : v ∈ C := rfl
  have hwC : w ∈ C :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj hvw).symm
  rw [color_eq_component G C v hvC, color_eq_component G C w hwC]
  exact componentColor_valid G C hv (show C.toSimpleGraph.Adj ⟨v, hvC⟩ ⟨w, hwC⟩ from hvw)

/-- The induced graph on all retained components is two-colorable. -/
theorem good_graph_colorable : (G.induce {v | Good G v}).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => color G v.val) ?_⟩
  intro v w hvw
  exact good_color_valid G v.property hvw

variable [Fintype V]

noncomputable def goodVertices : Finset V := by
  classical
  exact Finset.univ.filter (Good G)

@[simp] theorem mem_goodVertices (v : V) : v ∈ goodVertices G ↔ Good G v := by
  classical
  simp only [goodVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- At least half of all vertices in bipartite components can be selected
as one independent set. Component colorings and the large fiber are derived. -/
theorem exists_independent_good :
    ∃ I : Finset V, (∀ v ∈ I, Good G v) ∧ G.IsIndepSet (I : Set V) ∧
      (goodVertices G).card ≤ 2 * I.card := by
  classical
  obtain ⟨a, ha⟩ := exists_large_label_fiber (goodVertices G) (color G) (by decide)
  refine ⟨(goodVertices G).filter (fun v => color G v = a), ?_, ?_, ha⟩
  · intro v hv
    exact (mem_goodVertices G v).mp (Finset.mem_filter.mp hv).1
  · intro v hv w hw _ hvw
    have hv' := Finset.mem_filter.mp hv
    have hw' := Finset.mem_filter.mp hw
    exact good_color_valid G ((mem_goodVertices G v).mp hv'.1) hvw
      (hv'.2.trans hw'.2.symm)


end DeletionGraph.BipartiteSelection
namespace DeletionGraph.CodeSelection
open DeletionHash.MixedEdit
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] {n k L t b r : ℕ}

noncomputable def retained (ξ : HashSample α L r) : Finset (Word α n) := by
  classical
  exact Finset.univ.filter (fun x => IsUnique k (letters x) ∧
    ¬ (Exceptional n k t b ξ x ∨ BadComponent n k t b ξ x))

theorem component_good (ξ : HashSample α L r)
    (x : {x : Word α n // Good n k t b ξ x})
    (hx : ¬ BadComponent n k t b ξ x.val) :
    BipartiteSelection.Good (conflictGraph n k t b ξ) x := by
  classical
  have hc : ∃ color : {y : Word α n // Good n k t b ξ y} → Fin 2,
      ∀ y z, (conflictGraph n k t b ξ).Reachable x y →
        (conflictGraph n k t b ξ).Reachable x z →
        (conflictGraph n k t b ξ).Adj y z → color y ≠ color z := by
    by_contra hn
    exact hx ⟨x.property, hn⟩
  obtain ⟨color,hcolor⟩ := hc
  let C := (conflictGraph n k t b ξ).connectedComponentMk x
  refine ⟨SimpleGraph.Coloring.mk (fun y : C => color y.val) ?_⟩
  intro y z hyz
  exact hcolor y.val z.val (C.reachable_of_mem_supp rfl y.property)
    (C.reachable_of_mem_supp rfl z.property) hyz

theorem exists_code (ξ : HashSample α L r) :
    ∃ code : Finset (Word α n), Corrects b t code ∧
      (retained (n:=n) (k:=k) (t:=t) (b:=b) ξ).card ≤ 2 * 2^r * code.card := by
  classical
  let V := {x : Word α n // Good n k t b ξ x}
  letI : Fintype V := Fintype.ofFinite V
  let G := conflictGraph n k t b ξ
  have hret : (retained (n:=n) (k:=k) (t:=t) (b:=b) ξ).card ≤
      (BipartiteSelection.goodVertices G).card := by
    let S := retained (n:=n) (k:=k) (t:=t) (b:=b) ξ
    let f : {x // x ∈ S} → V := fun x =>
      ⟨x.val, (Finset.mem_filter.mp x.property).2.1,
        fun he => (Finset.mem_filter.mp x.property).2.2 (Or.inl he)⟩
    have hmap : ∀ x : {x // x ∈ S}, f x ∈ BipartiteSelection.goodVertices G := by
      intro x
      apply (BipartiteSelection.mem_goodVertices G _).mpr
      exact component_good ξ _ (fun hb => (Finset.mem_filter.mp x.property).2.2 (Or.inr hb))
    have hi : Function.Injective f := by
      intro x y he
      exact Subtype.ext (congrArg (fun z : V => z.val) he)
    calc
      S.card = S.attach.card := (Finset.card_attach (s:=S)).symm
      _ ≤ (BipartiteSelection.goodVertices G).card :=
        Finset.card_le_card_of_injOn f (fun x _ => hmap x) (hi.injOn)
  obtain ⟨I,_,hind,hhalf⟩ := BipartiteSelection.exists_independent_good G
  have hcardLabel : Fintype.card (Label r) = 2^r := by simp [Label, ZMod.card]
  let e : Label r ≃ Fin (2^r) := (Fintype.equivFin (Label r)).trans (finCongr hcardLabel)
  let label : V → Fin (2^r) := fun v => e (hash ξ (spectrum L (letters v.val)))
  obtain ⟨a,ha⟩ := BipartiteSelection.exists_large_label_fiber I label (Nat.succ_le_of_lt (pow_pos (by decide : 0<(2:ℕ)) r))
  let J := I.filter (fun v => label v = a)
  let code := J.image Subtype.val
  have hcard : code.card = J.card := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨code, ?_, ?_⟩
  · intro x hx y hy hxy hconf
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    have hv' := Finset.mem_filter.mp hv
    have hw' := Finset.mem_filter.mp hw
    have hne : v ≠ w := fun he => hxy (congrArg Subtype.val he)
    apply hind hv'.1 hw'.1 hne
    exact ⟨hne,hconf,e.injective (hv'.2.trans hw'.2.symm)⟩
  · rw [hcard, Nat.mul_assoc]
    exact hret.trans (hhalf.trans (Nat.mul_le_mul_left 2 ha))

end DeletionGraph.CodeSelection
namespace DeletionGraph.FiniteAverage
open DeletionHash.MixedEdit
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable

theorem probability_sum {Ω : Type u} [Fintype Ω] (P : Ω → Prop) :
    uniformProbability P = (∑ ω : Ω, if P ω then (1:ℝ) else 0) / Fintype.card Ω := by
  classical
  simp [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem half_retained {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    {V : Type v} (s : Finset V) (E : V → Ω → Prop)
    (hE : ∀ v ∈ s, uniformProbability (E v) ≤ (1:ℝ)/3) :
    ∃ ω, s.card ≤ 2 * (s.filter (fun v => ¬ E v ω)).card := by
  classical
  have hΩ : (0:ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hupper : (∑ ω : Ω, ((s.filter (fun v => E v ω)).card : ℝ)) ≤
      (s.card:ℝ) * Fintype.card Ω / 3 := by
    calc
      _ = ∑ v ∈ s, ∑ ω : Ω, if E v ω then (1:ℝ) else 0 := by
        simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        rw [Finset.sum_comm]
      _ ≤ ∑ _v ∈ s, (Fintype.card Ω:ℝ)/3 := by
        apply Finset.sum_le_sum
        intro v hv
        have h := hE v hv
        rw [probability_sum, div_le_iff₀ hΩ] at h
        linarith
      _ = _ := by simp; ring
  by_contra hnone
  have hpoint (ω : Ω) : (s.card:ℝ) < 2 * (s.filter (fun v => E v ω)).card := by
    have hn : ¬ s.card ≤ 2 * (s.filter (fun v => ¬ E v ω)).card := fun h => hnone ⟨ω,h⟩
    have hp := Finset.card_filter_add_card_filter_not (s := s) (fun v => E v ω)
    have h : s.card < 2 * (s.filter (fun v => E v ω)).card := by omega
    exact_mod_cast h
  have hsum := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset Ω))
    Finset.univ_nonempty (fun ω _ => hpoint ω)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hs : (0:ℝ) ≤ s.card := Nat.cast_nonneg _
  nlinarith

end DeletionGraph.FiniteAverage
namespace DeletionGraph.CodeParameters
open DeletionHash.MixedEdit

noncomputable def window (q b n : ℕ) : ℕ := 3*(uniqueLength q n+b+1)

theorem length_eq_clog (q n : ℕ) : uniqueLength q n = 2*Nat.clog q n+2 := by
  change 2*⌈Real.logb (q:ℝ) (n:ℝ)⌉₊+2 = _
  rw [Real.natCeil_logb_natCast]

theorem window_eq (q b n : ℕ) : window q b n = 6*Nat.clog q n+3*b+9 := by
  unfold window
  rw [length_eq_clog]
  omega

private theorem affine_le_pow (m : ℕ) : 10*(m+10) ≤ 2^(m+10) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show m+1+10=(m+10)+1 by omega, pow_succ]
    omega

def threshold (q b M : ℕ) : ℕ := q^(max (3*b+11) (max b M)) + q^q + 1

theorem ready (q t b M n : ℕ) (hq : 2≤q) (ht : 2≤t) (hb : 1≤b)
    (hn : threshold q b M ≤ n) :
    q^q ≤ n ∧ Regime q n t b (uniqueLength q n) (window q b n) ∧
      M ≤ window q b n := by
  have hc : max (3*b+11) (max b M) < Nat.clog q n := by
    apply (Nat.lt_clog_iff_pow_lt (by omega : 1<q)).mpr
    unfold threshold at hn
    omega
  have hnpow : q^(Nat.clog q n-1) < n :=
    Nat.pow_lt_of_lt_clog (by omega : Nat.clog q n-1 < Nat.clog q n)
  have hp := affine_le_pow (Nat.clog q n-11)
  rw [show Nat.clog q n-11+10=Nat.clog q n-1 by omega] at hp
  have hbase : 2^(Nat.clog q n-1) ≤ q^(Nat.clog q n-1) := Nat.pow_le_pow_left hq _
  have hfit : window q b n ≤ n := by rw [window_eq]; omega
  refine ⟨by unfold threshold at hn; omega, ?_, ?_⟩
  · refine ⟨hq,ht,hb,rfl,rfl,?_,hfit⟩
    rw [length_eq_clog]
    omega
  · rw [window_eq]
    omega

theorem log_large (q n : ℕ) (hq : 2≤q) (hn : q^q≤n) :
    (q:ℝ) ≤ Real.logb (q:ℝ) (n:ℝ) := by
  have hq' : (1:ℝ)<q := by exact_mod_cast (show 1<q by omega)
  have h := Real.logb_le_logb_of_le hq'
    (pow_pos (by linarith : (0:ℝ)<q) q) (show (q:ℝ)^q≤n by exact_mod_cast hn)
  simpa only [Real.logb_pow, Real.logb_self_eq_one hq', mul_one] using h

theorem loglog_one (q n : ℕ) (hq : 2≤q) (hn : q^q≤n) :
    1 ≤ Real.logb (q:ℝ) (Real.logb (q:ℝ) (n:ℝ)) := by
  have hq' : (1:ℝ)<q := by exact_mod_cast (show 1<q by omega)
  have h := Real.logb_le_logb_of_le hq' (by linarith : (0:ℝ)<q) (log_large q n hq hn)
  simpa only [Real.logb_self_eq_one hq'] using h

theorem log_window (q b n : ℕ) (hq : 2≤q) (hn : q^q≤n) :
    Real.logb (q:ℝ) (window q b n:ℝ) ≤
      (3*b+22:ℕ) * Real.logb (q:ℝ) (Real.logb (q:ℝ) (n:ℝ)) := by
  have hq' : (1:ℝ)<q := by exact_mod_cast (show 1<q by omega)
  have hlog : 1 ≤ Real.logb (q:ℝ) (n:ℝ) := by
    have := log_large q n hq hn
    have : (2:ℝ)≤q := by exact_mod_cast hq
    linarith
  have hceil : (Nat.clog q n:ℝ) < Real.logb (q:ℝ) (n:ℝ)+1 := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.ceil_lt_add_one (by linarith)
  have hL : (window q b n:ℝ) ≤ (3*b+21:ℕ)*Real.logb (q:ℝ) (n:ℝ) := by
    have he : (window q b n:ℝ)=6*(Nat.clog q n:ℝ)+3*b+9 := by exact_mod_cast window_eq q b n
    push_cast
    have hb : (0:ℝ)≤b := Nat.cast_nonneg _
    nlinarith
  have hd : 3*b+21 ≤ q^(3*b+21) :=
    (Nat.le_of_lt (Nat.lt_two_pow_self)).trans (Nat.pow_le_pow_left hq _)
  have hL' : (window q b n:ℝ) ≤ (q:ℝ)^(3*b+21)*Real.logb (q:ℝ) (n:ℝ) :=
    hL.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (by linarith))
  have hpos : (0:ℝ)<window q b n := by
    have he:=window_eq q b n
    exact_mod_cast (show 0<window q b n by omega)
  have h := Real.logb_le_logb_of_le hq' hpos hL'
  rw [Real.logb_mul (pow_ne_zero _ (by linarith : (q:ℝ)≠0)) (by linarith),
    Real.logb_pow, Real.logb_self_eq_one hq', mul_one] at h
  have hll := loglog_one q n hq hn
  have hb : (0:ℝ)≤b := Nat.cast_nonneg _
  push_cast at h ⊢
  nlinarith

end DeletionGraph.CodeParameters
namespace DeletionGraph.CodeRedundancy
open DeletionHash.MixedEdit
universe u

def coefficient (t b lam : ℕ) : ℕ := 6*b*t+8+lam*(3*b+22)

theorem bound {α : Type u} {n : ℕ} (q t b lam : ℕ)
    (code : Finset (Word α n)) (hq : 2≤q) (ht : 2≤t) (hn : q^q≤n)
    (hcard : q^n ≤ 64*q^(6*b*t+1)*n^(2*t-1)*(CodeParameters.window q b n)^lam*code.card) :
    code.Nonempty ∧ redundancy q code ≤
      ((2*t:ℝ)-1)*logBase q (n:ℝ) +
        (coefficient t b lam:ℝ)*logBase q (logBase q (n:ℝ)) := by
  have hq' : (1:ℝ)<q := by exact_mod_cast (show 1<q by omega)
  have hqp : (0:ℝ)<q := by linarith
  have hcp : 0<code.card := by
    have hp : 0<q^n := pow_pos (by omega) _
    by_contra h
    have hz : code.card=0 := by omega
    rw [hz,mul_zero] at hcard
    omega
  have hc : (0:ℝ)<code.card := by exact_mod_cast hcp
  have hnp : (0:ℝ)<n := by
    have hp : 0<q^q := pow_pos (by omega) _
    exact_mod_cast (show 0<n by omega)
  have hLp : (0:ℝ)<CodeParameters.window q b n := by
    have h:=CodeParameters.window_eq q b n
    exact_mod_cast (show 0<CodeParameters.window q b n by omega)
  have hreal : (q:ℝ)^n ≤ 64*(q:ℝ)^(6*b*t+1)*(n:ℝ)^(2*t-1)*
      (CodeParameters.window q b n:ℝ)^lam*(code.card:ℝ) := by exact_mod_cast hcard
  have hlog := Real.logb_le_logb_of_le hq' (pow_pos hqp n) hreal
  rw [Real.logb_mul (by positivity) (ne_of_gt hc),
    Real.logb_mul (by positivity) (pow_ne_zero _ (ne_of_gt hLp)),
    Real.logb_mul (by positivity) (pow_ne_zero _ (ne_of_gt hnp)),
    Real.logb_mul (by norm_num : (64:ℝ)≠0) (pow_ne_zero _ (ne_of_gt hqp))] at hlog
  simp only [Real.logb_pow, Real.logb_self_eq_one hq', mul_one] at hlog
  have h64 : Real.logb (q:ℝ) 64 ≤ 6 := by
    have hbase : (64:ℝ) ≤ (q:ℝ)^(6:ℕ) := by
      have h : (2:ℕ)^6≤q^6 := Nat.pow_le_pow_left hq 6
      norm_num at h
      exact_mod_cast h
    have h := Real.logb_le_logb_of_le hq' (by norm_num : (0:ℝ)<64) hbase
    simpa only [Real.logb_pow,Real.logb_self_eq_one hq',mul_one,Nat.cast_ofNat] using h
  have hw := mul_le_mul_of_nonneg_left (CodeParameters.log_window q b n hq hn)
    (Nat.cast_nonneg lam : (0:ℝ)≤lam)
  have hll := CodeParameters.loglog_one q n hq hn
  have he : ((2*t-1:ℕ):ℝ) = 2*(t:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤2*t)]
    push_cast
    rfl
  rw [he] at hlog
  refine ⟨Finset.card_pos.mp hcp,?_⟩
  change (n:ℝ)-Real.logb (q:ℝ) (code.card:ℝ) ≤
    (2*(t:ℝ)-1)*Real.logb (q:ℝ) (n:ℝ)+
      (coefficient t b lam:ℝ)*Real.logb (q:ℝ) (Real.logb (q:ℝ) (n:ℝ))
  have hd : (0:ℝ)≤6*b*t+8 := by positivity
  have hconst := mul_le_mul_of_nonneg_left hll hd
  unfold coefficient
  push_cast at hlog hw ⊢
  nlinarith

end DeletionGraph.CodeRedundancy
namespace DeletionGraph.DiscardBound
open DeletionHash.MixedEdit
universe u

theorem probability_or {Ω : Type u} [Fintype Ω] (P Q : Ω → Prop) :
    uniformProbability (fun ω => P ω ∨ Q ω) ≤ uniformProbability P + uniformProbability Q := by
  classical
  simp only [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.filter_or, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_union_le (Finset.univ.filter P) (Finset.univ.filter Q)

theorem exceptional_quarter {α : Type u} [Fintype α] [DecidableEq α]
    (q n k L t b lam r c : ℕ) (hqa : Fintype.card α=q)
    (hreg : Regime q n t b k L) (hlam : 2≤lam)
    (hconst : c ≤ L)
    (hQ : 4*q^(6*b*t+1)*n^(2*t-1)*L^lam≤2^r)
    (x : Word α n) (hx : IsUnique k (letters x))
    (hbound : uniformProbability (fun ξ : HashSample α L r => Exceptional n k t b ξ x) ≤
      (c:ℝ)*(q:ℝ)^(2*b*t)*(L:ℝ)*(n:ℝ)^(2*t-1)/(2:ℝ)^r) :
    uniformProbability (fun ξ : HashSample α L r => Exceptional n k t b ξ x) ≤ (1:ℝ)/4 := by
  have he := hbound
  obtain ⟨hq,ht,hb,hk,hL,hbk,hLn⟩ := hreg
  have hL1 : 1≤L := by omega
  have hpow : q^(2*b*t)≤q^(6*b*t+1) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hwin : c * L ≤ L^lam := by
    calc
      _ ≤ L*L := Nat.mul_le_mul_right L hconst
      _ = L^2 := by ring
      _ ≤ L^lam := Nat.pow_le_pow_right hL1 hlam
  have hnum : c * q^(2*b*t)*L*n^(2*t-1) ≤
      q^(6*b*t+1)*n^(2*t-1)*L^lam := by
    calc
      _ = (c*L)*q^(2*b*t)*n^(2*t-1) := by ring
      _ ≤ L^lam*q^(6*b*t+1)*n^(2*t-1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul hwin hpow)
      _ = _ := by ring
  have hnumR : (c:ℝ)*(q:ℝ)^(2*b*t)*L*(n:ℝ)^(2*t-1) ≤
      (q:ℝ)^(6*b*t+1)*(n:ℝ)^(2*t-1)*(L:ℝ)^lam := by exact_mod_cast hnum
  have hQR : 4*(q:ℝ)^(6*b*t+1)*(n:ℝ)^(2*t-1)*(L:ℝ)^lam≤(2:ℝ)^r := by exact_mod_cast hQ
  apply he.trans
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^r)).mpr
  nlinarith

end DeletionGraph.DiscardBound
namespace DeletionGraph.CodeExistence
open DeletionHash.MixedEdit
universe u

theorem large_code {α : Type u} [Fintype α] [DecidableEq α]
    (q n k L t b r : ℕ) (hqa : Fintype.card α=q)
    (hreg : Regime q n t b k L)
    (hexc : ∀ x : Word α n, IsUnique k (letters x) →
      uniformProbability (fun ξ : HashSample α L r => Exceptional n k t b ξ x) ≤ (1:ℝ)/4)
    (hbad : ∀ x : Word α n, IsUnique k (letters x) →
      uniformProbability (fun ξ : HashSample α L r => BadComponent n k t b ξ x) ≤ (1:ℝ)/12) :
    ∃ code : Finset (Word α n), Corrects b t code ∧ q^n ≤ 8*2^r*code.card := by
  classical
  let s := uniqueFamily α n k
  let E : Word α n → HashSample α L r → Prop := fun x ξ =>
    Exceptional n k t b ξ x ∨ BadComponent n k t b ξ x
  obtain ⟨ξ,hhalf⟩ := FiniteAverage.half_retained s E (by
    intro x hx
    have hu : IsUnique k (letters x) := by simpa only [s,uniqueFamily,Finset.mem_filter,Finset.mem_univ,true_and] using hx
    have he := hexc x hu
    have hb := hbad x hu
    have h := DiscardBound.probability_or
      (fun ξ : HashSample α L r => Exceptional n k t b ξ x)
      (fun ξ => BadComponent n k t b ξ x)
    exact h.trans (by linarith))
  have hret : s.filter (fun x => ¬ E x ξ) = CodeSelection.retained (n:=n) (k:=k) (t:=t) (b:=b) ξ := by
    ext x
    simp [s,uniqueFamily,E,CodeSelection.retained]
  have hhalf' : s.card ≤ 2*(CodeSelection.retained (n:=n) (k:=k) (t:=t) (b:=b) ξ).card := by
    convert hhalf using 1
    congr 2
    ext x
    simp [CodeSelection.retained,s,uniqueFamily,E]

  obtain ⟨code,hcorrect,hselect⟩ := CodeSelection.exists_code (n:=n) (k:=k) (t:=t) (b:=b) ξ
  obtain ⟨hq,ht,hb,hk,hL,hbk,hLn⟩ := hreg
  have hn : 1≤n := by omega
  have hmass := DeletionHash.MixedEdit.most_words_unique (α:=α) n hn (by omega)
  dsimp only at hmass
  rw [hqa, ← hk] at hmass
  have hreal : (q:ℝ)^n ≤ 2*(s.card:ℝ) := by
    dsimp only [s]
    linarith [hmass.1,hmass.2.1,hmass.2.2]
  have hnat : q^n ≤ 2*s.card := by exact_mod_cast hreal
  refine ⟨code,hcorrect,?_⟩
  calc
    q^n ≤ 2*s.card := hnat
    _ ≤ 2*(2*(2*2^r*code.card)) := Nat.mul_le_mul_left 2
      (hhalf'.trans (Nat.mul_le_mul_left 2 hselect))
    _ = _ := by ring

end DeletionGraph.CodeExistence
namespace DeletionGraph.SubstringTheorem
open DeletionHash.MixedEdit

universe u

/-- Theorems 1.2 and 6.2: C is chosen before q, and N before the alphabet type. -/
theorem codes (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∃ N : ℕ, q^q ≤ N ∧
      ∀ (α : Type u) [Fintype α] [DecidableEq α], Fintype.card α = q →
      ∀ n : ℕ, N ≤ n → ∃ code : Finset (Word α n), code.Nonempty ∧ Corrects b t code ∧
        redundancy q code ≤ ((2*t : ℝ)-1)*logBase q (n : ℝ) + C*logBase q (logBase q (n : ℝ)) := by
  classical
  obtain ⟨a,ha,hcount,lam,L₀,hlam,hL₀,hexp,hprob⟩ := DeletionHash.MixedEdit.odd_cycles_rare.{u} t b ht hb
  refine ⟨(CodeRedundancy.coefficient t b lam:ℝ), ?_, ?_⟩
  · unfold CodeRedundancy.coefficient
    positivity
  intro q hq
  obtain ⟨c,hc,hthin⟩ := DeletionHash.MixedEdit.nonseparated_thin.{u} t b ht hb
  let M := max L₀ ⌈c⌉₊
  let N := CodeParameters.threshold q b M
  refine ⟨N, ?_, ?_⟩
  · dsimp [N,CodeParameters.threshold]
    omega
  intro α instF instD hqa n hn
  let k := uniqueLength q n
  let L := CodeParameters.window q b n
  obtain ⟨hnq,hreg,hM⟩ := CodeParameters.ready q t b M n hq ht hb hn
  have hreg' : Regime q n t b k L := hreg
  have hLpos : 1≤L := by
    have he:=CodeParameters.window_eq q b n
    dsimp only [L]
    omega
  have hnpos : 1≤n := by
    have hp : 0<q^q := pow_pos (by omega) _
    omega
  let A := 4*q^(6*b*t+1)*n^(2*t-1)*L^lam
  have hA : 1<A := by
    have hqp : 0<q^(6*b*t+1) := pow_pos (by omega) _
    have hnp : 0<n^(2*t-1) := pow_pos (by omega) _
    have hLp : 0<L^lam := pow_pos (by omega) _
    have hp : 1≤q^(6*b*t+1)*n^(2*t-1)*L^lam :=
      Nat.succ_le_of_lt (mul_pos (mul_pos hqp hnp) hLp)
    calc
      1 < 4 := by decide
      _ = 4*1 := by omega
      _ ≤ 4*(q^(6*b*t+1)*n^(2*t-1)*L^lam) := Nat.mul_le_mul_left 4 hp
      _ = A := by dsimp only [A]; ring
  let r := Nat.clog 2 A
  have hr : 1≤r := Nat.clog_pos (by decide) hA
  have hQ : A≤2^r := Nat.le_pow_clog (by decide) A
  have hround : 2^r≤2*A := by
    have hp : 2^(r-1)<A := Nat.pow_lt_of_lt_clog (by omega : r-1<r)
    calc
      2^r=2*2^(r-1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hr]
        rw [pow_succ,Nat.mul_comm]
      _ ≤ 2*A := Nat.mul_le_mul_left 2 hp.le
  have hquarter (x : Word α n) (hx : IsUnique k (letters x)) :
      uniformProbability (fun ξ : HashSample α L r => Exceptional n k t b ξ x) ≤ (1:ℝ)/4 := by
    apply DiscardBound.exceptional_quarter q n k L t b lam r ⌈c⌉₊ hqa hreg'
      hlam (by dsimp only [M] at hM; omega) hQ x hx
    apply (hthin q α hqa n k L r hreg' hr x hx).trans
    gcongr
    exact Nat.le_ceil c
  obtain ⟨code,hcorrect,hcard⟩ := CodeExistence.large_code q n k L t b r hqa hreg' hquarter
    (hprob q α hqa n k L r hreg' (by dsimp only [M] at hM; omega) hr hQ)
  have hcard' : q^n≤64*q^(6*b*t+1)*n^(2*t-1)*L^lam*code.card := by
    calc
      q^n ≤ 8*2^r*code.card := hcard
      _ ≤ 8*(2*A)*code.card := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 hround)
      _ = _ := by dsimp only [A]; ring
  obtain ⟨hne,hred⟩ := CodeRedundancy.bound q t b lam code hq ht hnq hcard'
  exact ⟨code,hne,hcorrect,hred⟩

end DeletionGraph.SubstringTheorem

open DeletionHash.MixedEdit

universe u

/-- Theorems 1.2 and 6.2: C is chosen before q, and N before the alphabet type. -/
theorem solution (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∃ N : ℕ, q^q ≤ N ∧
      ∀ (α : Type u) [Fintype α] [DecidableEq α], Fintype.card α = q →
      ∀ n : ℕ, N ≤ n → ∃ code : Finset (Word α n), code.Nonempty ∧ Corrects b t code ∧
        redundancy q code ≤ ((2*t : ℝ)-1)*logBase q (n : ℝ) + C*logBase q (logBase q (n : ℝ)) := by exact DeletionGraph.SubstringTheorem.codes t b ht hb



#print axioms solution
