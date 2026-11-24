-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.col_lead
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:54:14.108846+00:00
-- url     : https://prove2.me/submissions/169dabcf-d440-4764-9e2c-2297f8851bdb

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_LeadAt_of_hom
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_LeadAt_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_weight_wt
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_wt_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_wt_lt
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_wedge_term
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_contr_term
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_isWeightedHomogeneous_zero_stripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_sg_pm
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_colHeight_le
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_path_height

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace A1
section Top
variable {σ R M : Type*} [CommRing R] [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]
end Top
section Col
variable {R M : Type*} [CommRing R] [AddCommMonoid M] {n : ℕ}
private theorem stripPathWord_succ_eq_lemma_2 {R : Type*} [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (Xr : ℕ → Fin n → R) (i : ℕ) :
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c Xr (i + 1) = if Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (i + 1)) c = Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ i) c then
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c Xr i else Formalism.InvariantFactorPaths.GelfandTsetlinBases.stepF (isVec i == decide (1 ≤ c)) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c Xr i) (Xr i) := by
  rfl
end Col
private theorem erase_seg_lemma_4 {n : ℕ} (k : ℕ) (t : Fin n) (ht : t.val = k) :
    (univ.filter fun m : Fin n => m.val < k + 1).erase t = univ.filter fun m : Fin n => m.val < k := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  rw [Fin.ext_iff]
  constructor <;> intro h <;> omega
private theorem insert_seg_lemma_5 {n : ℕ} (k : ℕ) (t : Fin n) (ht : t.val = k) :
    insert t (univ.filter fun m : Fin n => m.val < k) = univ.filter fun m : Fin n => m.val < k + 1 := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fin.ext_iff]
  constructor <;> intro h <;> omega
private theorem erase_coseg_lemma_6 {n : ℕ} (k : ℕ) (t : Fin n) (ht : t.val = k) :
    (univ.filter fun m : Fin n => k ≤ m.val).erase t = univ.filter fun m : Fin n => k + 1 ≤ m.val := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  rw [Fin.ext_iff]
  constructor <;> intro h <;> omega
private theorem insert_coseg_lemma_7 {n : ℕ} (k : ℕ) (t : Fin n) (ht : t.val = k) :
    insert t (univ.filter fun m : Fin n => k + 1 ≤ m.val) = univ.filter fun m : Fin n => k ≤ m.val := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fin.ext_iff]
  constructor <;> intro h <;> omega
private theorem stepForm_true_lemma_10 {R : Type*} [CommRing R] {n : ℕ} {up : Bool} (h : up = true) (K : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Form R n)
    (Xv : Fin n → R) : Formalism.InvariantFactorPaths.GelfandTsetlinBases.stepF up K Xv = Formalism.InvariantFactorPaths.GelfandTsetlinBases.wedgeF K Xv := by
  subst h
  rfl
private theorem stepForm_false_lemma_11 {R : Type*} [CommRing R] {n : ℕ} {up : Bool} (h : up = false) (K : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Form R n)
    (Xv : Fin n → R) : Formalism.InvariantFactorPaths.GelfandTsetlinBases.stepF up K Xv = Formalism.InvariantFactorPaths.GelfandTsetlinBases.contrF K Xv := by
  subst h
  rfl
private theorem leading_wedge_lemma_12 {R : Type*} [CommRing R] {n N : ℕ} (v : Bool)
    (K : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Form (MvPolynomial (ℕ × Fin n) R) n)
    (hK : ∀ J, IsWeightedHomogeneous (wt n N v) (K J) 0)
    (I : Finset (Fin n)) (top : Fin n) (htop : top ∈ I)
    (hlt : ∀ m ∈ I, m ≠ top → wt n N v (N, m) < wt n N v (N, top)) :
    LeadAt (wt n N v) (wt n N v (N, top)) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.wedgeF K (XR R n N) I)
      (((Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg I top : ℤ) : MvPolynomial (ℕ × Fin n) R) * K (I.erase top) * XR R n N top) :=
  Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.sum I (fun m => wt n N v (N, m))
    (fun m => ((Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg I m : ℤ) : MvPolynomial (ℕ × Fin n) R) * K (I.erase m) * XR R n N m)
    (fun m _ => wedge_term _ K hK N I m) top htop hlt
private theorem leading_contract_lemma_13 {R : Type*} [CommRing R] {n N : ℕ} (v : Bool)
    (K : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Form (MvPolynomial (ℕ × Fin n) R) n)
    (hK : ∀ J, IsWeightedHomogeneous (wt n N v) (K J) 0)
    (I : Finset (Fin n)) (top : Fin n) (htop : top ∉ I)
    (hlt : ∀ m ∈ Iᶜ, m ≠ top → wt n N v (N, m) < wt n N v (N, top)) :
    LeadAt (wt n N v) (wt n N v (N, top)) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.contrF K (XR R n N) I)
      (((Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg I top : ℤ) : MvPolynomial (ℕ × Fin n) R) * K (insert top I) * XR R n N top) := by
  rw [mul_right_comm]
  exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.sum Iᶜ (fun m => wt n N v (N, m))
    (fun m => ((Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg I m : ℤ) : MvPolynomial (ℕ × Fin n) R) * XR R n N m * K (insert m I))
    (fun m _ => contr_term _ K hK N I m) top (Finset.mem_compl.mpr htop) hlt
private theorem monomial_zero_one_eq_lemma_14 {σ R : Type*} [CommRing R] :
    (monomial (0 : σ →₀ ℕ) (1 : R) : MvPolynomial σ R) = 1 := by
  rfl
end A1
namespace A1
end A1
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution (R : Type*) [CommRing R] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ (N + 1)) (c : ℤ) :
    ∃ a : ℤ, (a = 1 ∨ a = -1) ∧
      LeadAt (wt n N (isVec N)) (Finsupp.weight (wt n N (isVec N)) (Dc μ N c))
        (pathWord isVec μ c (XR R n) (N + 1) (canIdx (μ (N + 1)) c))
        ((a : MvPolynomial (ℕ × Fin n) R) * pathWord isVec μ c (XR R n) N (canIdx (μ N) c) *
          monomial (Dc μ N c) 1) := by
  classical
  have hK : ∀ J, IsWeightedHomogeneous (wt n N (isVec N))
      (Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c (XR R n) N J) 0 :=
    isWeightedHomogeneous_zero_stripPathWord (R := R) (wt n N (isVec N)) N
      (fun x hx => wt_zero (isVec N) hx) isVec μ c N le_rfl
  have hstep := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.path_height hp (Nat.lt_succ_self N) c
  have hle1 := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.colHeight_le (μ (N + 1)) c
  have hle0 := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.colHeight_le (μ N) c
  by_cases hch : Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c = Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c
  · refine ⟨1, Or.inl rfl, ?_⟩
    have hcj : Dc μ N c = 0 := by
      unfold Dc
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [if_neg]
      exact fun h => h.1 hch
    have hci : Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ (N + 1)) c = Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ N) c := by
      unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx
      rw [hch]
    rw [hcj, map_zero, hci, stripPathWord_succ_eq_lemma_2, if_pos hch, Int.cast_one, one_mul, monomial_zero_one_eq_lemma_14, mul_one]
    exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.of_hom (hK _)
  · have hmin : min (Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c) < n := by
      rcases Nat.lt_or_gt_of_ne hch with h | h
      · exact lt_of_le_of_lt (min_le_left _ _) (lt_of_lt_of_le h hle0)
      · exact lt_of_le_of_lt (min_le_right _ _) (lt_of_lt_of_le h hle1)
    obtain ⟨top, htopv⟩ : ∃ t : Fin n, t.val = min (Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c) :=
      ⟨⟨_, hmin⟩, rfl⟩
    have hcj : Dc μ N c = Finsupp.single (N, top) 1 := by
      unfold Dc
      rw [Finset.sum_eq_single top]
      · rw [if_pos ⟨hch, htopv⟩]
      · intro m _ hm
        rw [if_neg]
        rintro ⟨_, h⟩
        exact hm (Fin.ext (h.trans htopv.symm))
      · intro h
        exact absurd (Finset.mem_univ top) h
    have hmono : (monomial (Dc μ N c) (1 : R) : MvPolynomial (ℕ × Fin n) R) = XR R n N top := by
      rw [hcj]
      rfl
    have hlev : Finsupp.weight (wt n N (isVec N)) (Dc μ N c) = wt n N (isVec N) (N, top) := by
      rw [hcj, weight_wt]
      rfl
    rw [hmono, hlev, stripPathWord_succ_eq_lemma_2, if_neg hch]
    by_cases hv : isVec N = true
    · rw [if_pos hv] at hstep
      have hb : Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c = Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c + 1 := hstep.resolve_left hch
      have htv : top.val = Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c := by
        rw [htopv, hb]
        exact min_eq_right (Nat.le_succ _)
      have hord : ∀ m : Fin n, m.val < top.val →
          wt n N (isVec N) (N, m) < wt n N (isVec N) (N, top) := fun m hm =>
        wt_lt (isVec N) (by rw [if_pos hv]; exact Fin.lt_def.mpr hm)
      by_cases hc : 1 ≤ c
      · have hup : (isVec N == decide (1 ≤ c)) = true := by
          rw [hv, decide_eq_true hc]
          rfl
        have hI1 : Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ (N + 1)) c =
            univ.filter (fun m : Fin n => m.val < Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c + 1) := by
          unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx
          rw [if_pos hc, hb]
        have hI0 : Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ N) c =
            (univ.filter (fun m : Fin n => m.val < Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c + 1)).erase top := by
          rw [erase_seg_lemma_4 _ top htv]
          unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx
          rw [if_pos hc]
        rw [stepForm_true_lemma_10 hup, hI1, hI0]
        refine ⟨_, sg_pm _ top, leading_wedge_lemma_12 (isVec N) _ hK _ top ?_ ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
        · intro m hm hne
          have hm' : m.val < Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c + 1 := (Finset.mem_filter.mp hm).2
          have hne' : m.val ≠ top.val := fun h => hne (Fin.ext h)
          exact hord m (by omega)
      · have hup : (isVec N == decide (1 ≤ c)) = false := by
          rw [hv, decide_eq_false hc]
          rfl
        have hI1 : Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ (N + 1)) c =
            univ.filter (fun m : Fin n => Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c + 1 ≤ m.val) := by
          unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx
          rw [if_neg hc, hb]
        have hI0 : Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ N) c =
            insert top (univ.filter (fun m : Fin n => Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c + 1 ≤ m.val)) := by
          rw [insert_coseg_lemma_7 _ top htv]
          unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx
          rw [if_neg hc]
        rw [stepForm_false_lemma_11 hup, hI1, hI0]
        refine ⟨_, sg_pm _ top, leading_contract_lemma_13 (isVec N) _ hK _ top ?_ ?_⟩
        · intro h
          have := (Finset.mem_filter.mp h).2
          omega
        · intro m hm hne
          have hm' : ¬ (Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c + 1 ≤ m.val) := fun h =>
            Finset.mem_compl.mp hm (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have hne' : m.val ≠ top.val := fun h => hne (Fin.ext h)
          exact hord m (by omega)
    · rw [if_neg hv] at hstep
      have hb : Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c + 1 = Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c := hstep.resolve_left hch
      have htv : top.val = Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c := by
        rw [htopv]
        exact min_eq_left (by omega)
      have hv' : isVec N = false := by simpa using hv
      have hord : ∀ m : Fin n, top.val < m.val →
          wt n N (isVec N) (N, m) < wt n N (isVec N) (N, top) := fun m hm =>
        wt_lt (isVec N) (by rw [if_neg hv]; exact Fin.lt_def.mpr hm)
      by_cases hc : 1 ≤ c
      · have hup : (isVec N == decide (1 ≤ c)) = false := by
          rw [hv', decide_eq_true hc]
          rfl
        have hI1 : Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ (N + 1)) c =
            univ.filter (fun m : Fin n => m.val < Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c) := by
          unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx
          rw [if_pos hc]
        have hI0 : Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ N) c =
            insert top (univ.filter (fun m : Fin n => m.val < Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c)) := by
          rw [insert_seg_lemma_5 _ top htv]
          unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx
          rw [if_pos hc, hb]
        rw [stepForm_false_lemma_11 hup, hI1, hI0]
        refine ⟨_, sg_pm _ top, leading_contract_lemma_13 (isVec N) _ hK _ top ?_ ?_⟩
        · intro h
          have := (Finset.mem_filter.mp h).2
          omega
        · intro m hm hne
          have hm' : ¬ (m.val < Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c) := fun h =>
            Finset.mem_compl.mp hm (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have hne' : m.val ≠ top.val := fun h => hne (Fin.ext h)
          exact hord m (by omega)
      · have hup : (isVec N == decide (1 ≤ c)) = true := by
          rw [hv', decide_eq_false hc]
          rfl
        have hI1 : Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ (N + 1)) c =
            univ.filter (fun m : Fin n => Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c ≤ m.val) := by
          unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx
          rw [if_neg hc]
        have hI0 : Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ N) c =
            (univ.filter (fun m : Fin n => Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c ≤ m.val)).erase top := by
          rw [erase_coseg_lemma_6 _ top htv]
          unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx
          rw [if_neg hc, hb]
        rw [stepForm_true_lemma_10 hup, hI1, hI0]
        refine ⟨_, sg_pm _ top, leading_wedge_lemma_12 (isVec N) _ hK _ top ?_ ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
        · intro m hm hne
          have hm' : Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c ≤ m.val := (Finset.mem_filter.mp hm).2
          have hne' : m.val ≠ top.val := fun h => hne (Fin.ext h)
          exact hord m (by omega)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
