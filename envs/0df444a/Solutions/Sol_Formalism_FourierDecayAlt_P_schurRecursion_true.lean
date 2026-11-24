-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.schurRecursion_true
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:55.244835+00:00
-- url     : https://prove2.me/submissions/dc18cdb4-a8d5-4bcb-8c50-85c28a154dbd

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockStartPoints
import Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_Xs_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_schur_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_phi_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_diag_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_Sf_pts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.BlockStartPoints
open Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TB.SchurStep := by
  intro E W _ D ep hG hK hW hA2 hEL hLS T ε hε i s hs hsi hi w hw hcnt M hM
  have hlev : ∀ h ∈ T.X (i - s), level h = i - s := fun h hh => ((T.isTower _ _).1 hh).1
  have hS0 : ∀ t ∈ T.Sg (i - s + 1) s, t ≠ 0 := fun t ht h0 => T.zero_not_mem _ _ (h0 ▸ ht)
  have hep : 0 ≤ ep := by simpa using hLS.1 i (by omega) hi ∅ (by simp)
  have ha : ∀ w' t, 0 ≤ (D.Nst ε i s w' (T.X (i - s)) (blk (D.Kr i) s t t) t t).re :=
    fun w' t => diag_nonneg D hG hK hW ε hε i s w' _ t
  have hM0 : 0 ≤ M :=
    le_trans (Finset.sum_nonneg fun t _ => ha w t) (hM w (by simp [Data.Wb, hw]))
  rw [Xs_eq T i s hs hsi, Sf_pts]
  generalize hY : T.X (i - s) = Y at *
  generalize hS : T.Sg (i - s + 1) s = S at *
  have hDg : ∀ w', D.Dg T ε i s w' =
      ∑ t ∈ S, (D.Nst ε i s w' Y (blk (D.Kr i) s t t) t t).re := by
    intro w'; unfold Data.Dg; rw [hY, hS]
  simp only [hDg] at hM ⊢

  have hz : ∀ t ∈ S, ∀ t' ∈ S, t ≠ t' →
      ((i = D.r + 1 ∧ s = 1) ∨ t⁻¹ - t'⁻¹ ∉ D.Lap (i - s + 1) s) →
      D.Nst ε i s w Y (blk (D.Kr i) s t t') t t' = 0 := by
    intro t ht t' ht' hne hc
    unfold Data.Nst
    rw [Finset.sum_eq_zero, zero_div]
    intro h hh
    refine Finset.sum_eq_zero fun h' hh' => ?_
    have hk0 : D.Kr i (join h s t) (join h' s t') = 0 := by
      by_contra hk
      obtain ⟨h1, h2⟩ := hA2 i s hs hsi hi h h' t t' (hlev h hh) (hlev h' hh') (hS0 t ht)
        (hS0 t' ht') hne hk
      rcases hc with hc | hc
      · exact h1 hc
      · exact hc h2
    simp [blk, hk0]

  have split : ∀ B : E → E → ℝ,
      (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → (D.Nst ε i s w Y (blk (D.Kr i) s t t') t t').re ≤ B t t') →
      (∀ t, 0 ≤ B t t) →
      ∑ t ∈ S, ∑ t' ∈ S, (D.Nst ε i s w Y (blk (D.Kr i) s t t') t t').re ≤
        ∑ t ∈ S, (D.Nst ε i s w Y (blk (D.Kr i) s t t) t t).re + ∑ t ∈ S, ∑ t' ∈ S, B t t' := by
    intro B hB hB0
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t ht => ?_
    have e : (D.Nst ε i s w Y (blk (D.Kr i) s t t) t t).re =
        ∑ t' ∈ S, if t' = t then (D.Nst ε i s w Y (blk (D.Kr i) s t' t') t' t').re else 0 := by
      rw [Finset.sum_ite_eq' S t, if_pos ht]
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t' ht' => ?_
    by_cases htt : t' = t
    · subst htt
      rw [if_pos rfl]
      linarith [hB0 t']
    · rw [if_neg htt, zero_add]
      exact hB t ht t' ht' (Ne.symm htt)
  by_cases htop : i = D.r + 1 ∧ s = 1
  · have h1 := split (fun _ _ => 0)
      (fun t ht t' ht' hne => by rw [hz t ht t' ht' hne (Or.inl htop)]; simp) (fun _ => le_rfl)
    have h2 : 0 ≤ 3 ^ D.f * ep * M := by positivity
    simp only [Finset.sum_const_zero, add_zero] at h1
    linarith
  obtain ⟨θ, hθ, hE⟩ := hEL ε hε i s hs hsi hi htop w hw hcnt
  have hE' := hE Y S (D.Kr i) hlev (hK.1 i _)
  set WW := D.Wb (D.cnt w + D.K) ×ˢ D.Wb (D.cnt w + D.K) with hWW
  set ρ := D.szL (i - s + 1) s with hρ
  set a : W → E → ℝ := fun w' t => (D.Nst ε i s w' Y (blk (D.Kr i) s t t) t t).re with hadef

  let P : E → E → Prop := fun t t' =>
    t ≠ t' ∧ t⁻¹ - t'⁻¹ ∈ D.Lap (i - s + 1) s ∧ 0 ≤ D.maj ρ (t⁻¹ - t'⁻¹)
  let m : E → E → ℝ := fun t t' => if P t t' then D.maj ρ (t⁻¹ - t'⁻¹) else 0
  have hm0 : ∀ t t', 0 ≤ m t t' := by
    intro t t'
    by_cases hP : P t t'
    · simp only [m, if_pos hP]; exact hP.2.2
    · simp only [m, if_neg hP]; exact le_rfl
  have row : ∀ t ∈ S, ∑ t' ∈ S, m t t' ≤ ep := by
    intro t _
    have h1 := hLS.2 i s hs hsi hi htop ((S.filter fun t' => P t t').image fun t' => t⁻¹ - t'⁻¹)
      (by
        intro l hl
        obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hl
        have hP := (Finset.mem_filter.1 ht').2
        exact ⟨hP.2.1, sub_ne_zero.2 fun e => hP.1 (inv_injective e)⟩)
    rw [Finset.sum_image (by
      intro x _ y _ e
      exact inv_injective (sub_right_injective e)), Finset.sum_filter] at h1
    exact h1
  have col : ∀ t' ∈ S, ∑ t ∈ S, m t t' ≤ ep := by
    intro t' _
    have h1 := hLS.2 i s hs hsi hi htop ((S.filter fun t => P t t').image fun t => t⁻¹ - t'⁻¹)
      (by
        intro l hl
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hl
        have hP := (Finset.mem_filter.1 ht).2
        exact ⟨hP.2.1, sub_ne_zero.2 fun e => hP.1 (inv_injective e)⟩)
    rw [Finset.sum_image (by
      intro x _ y _ e
      exact inv_injective (sub_left_injective e)), Finset.sum_filter] at h1
    exact h1
  have hX0 : ∀ π t t', 0 ≤ ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) := by
    intro π t t'
    refine Finset.sum_nonneg fun x _ => mul_nonneg ((hθ π).1 x) ?_
    have := ha x.1 t
    have := ha x.2 t'
    simp only [hadef]
    linarith
  have h1 := split (fun t t' => m t t' * ∑ π, ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2))
    (by
      intro t ht t' ht' hne
      have hG0 : 0 ≤ ∑ π, ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) :=
        Finset.sum_nonneg fun π _ => hX0 π t t'
      by_cases hL : t⁻¹ - t'⁻¹ ∈ D.Lap (i - s + 1) s
      · obtain ⟨π, hπ⟩ := hE' t ht t' ht' (hS0 t ht) (hS0 t' ht')
          (sub_ne_zero.2 fun e => hne (inv_injective e))
        have h2 : (D.Nst ε i s w Y (blk (D.Kr i) s t t') t t').re ≤
            D.maj ρ (t⁻¹ - t'⁻¹) * ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) :=
          le_trans (Complex.re_le_norm _) hπ
        have h3 : ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) ≤
            ∑ π, ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) :=
          Finset.single_le_sum (f := fun π => ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2))
            (fun π _ => hX0 π t t') (Finset.mem_univ π)
        by_cases hmj : 0 ≤ D.maj ρ (t⁻¹ - t'⁻¹)
        · have hP : P t t' := ⟨hne, hL, hmj⟩
          simp only [m, if_pos hP]
          exact le_trans h2 (mul_le_mul_of_nonneg_left h3 hmj)
        · have h4 : D.maj ρ (t⁻¹ - t'⁻¹) * ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (not_le.1 hmj).le (hX0 π t t')
          exact le_trans (le_trans h2 h4) (mul_nonneg (hm0 t t') hG0)
      · rw [hz t ht t' ht' hne (Or.inr hL)]
        exact mul_nonneg (hm0 t t') hG0)
    (fun t => mul_nonneg (hm0 t t) (Finset.sum_nonneg fun π _ => hX0 π t t))
  refine le_trans h1 (add_le_add le_rfl ?_)
  rw [phi_sum]
  have h5 : ∀ π : Fin D.f → Fin 3,
      ∑ t ∈ S, ∑ t' ∈ S, m t t' * ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2) ≤ ep * M := by
    intro π
    rw [phi_sum]
    calc ∑ x ∈ WW, ∑ t ∈ S, ∑ t' ∈ S, m t t' * (θ π x * ((a x.1 t + a x.2 t') / 2))
        = ∑ x ∈ WW, θ π x * ∑ t ∈ S, ∑ t' ∈ S, m t t' * ((a x.1 t + a x.2 t') / 2) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t' _ => by ring
      _ ≤ ∑ x ∈ WW, θ π x * (ep * M) := by
          refine Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left ?_ ((hθ π).1 x)
          have hx' := Finset.mem_product.1 hx
          exact schur_real S m ep M hep row col (a x.1) (a x.2) (ha x.1) (ha x.2)
            (hM x.1 hx'.1) (hM x.2 hx'.2)
      _ = ep * M := by rw [← Finset.sum_mul, (hθ π).2.2, one_mul]
  calc ∑ π : Fin D.f → Fin 3,
        ∑ t ∈ S, ∑ t' ∈ S, m t t' * ∑ x ∈ WW, θ π x * ((a x.1 t + a x.2 t') / 2)
      ≤ ∑ _π : Fin D.f → Fin 3, ep * M := Finset.sum_le_sum fun π _ => h5 π
    _ = 3 ^ D.f * ep * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
end Formalism.FourierDecayAlt.P
