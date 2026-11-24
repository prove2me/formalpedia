-- Prove2me | solution 1 for Formalism.REAL.hVCoeff_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:00:15.547673+00:00
-- url     : https://prove2.me/submissions/c1226343-d665-4714-b6e4-5b94d00a45ca

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
import Theorems.Thm_Formalism_REAL_fin_one_fun_eq_const_apply_zero
import Theorems.Thm_Formalism_REAL_arr_operator_one_apply
import Theorems.Thm_Formalism_REAL_noncompact_arr_one_values
import Theorems.Thm_Formalism_REAL_compact_highest_weight_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (hl : KLow) (hw : KWtOrth) (ha : ArrModule) : HVCoeff := by
  intro V _ _ n ε E Λ μ u F hg hu hΛ hF hFh hF0
  classical
  set f : Fin n × Fin n → V := fun p => F (fun _ => p) with hf
  have hnz : ∃ p, f p ≠ 0 := by
    by_contra h
    push Not at h
    apply hF0
    apply PiLp.ext
    intro α
    rw [fin_one_fun_eq_const_apply_zero α]
    simpa [hf] using h (α 0)
  obtain ⟨⟨a, b⟩, hpP, hmax⟩ := (univ.filter (fun p => f p ≠ 0)).exists_max_image
    (fun p : Fin n × Fin n => ((p.1 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ))
    (by obtain ⟨p, hp⟩ := hnz; exact ⟨p, by simp [hp]⟩)
  have hzero : ∀ q : Fin n × Fin n, ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) < ((q.1 : ℕ) : ℤ) - ((q.2 : ℕ) : ℤ) →
      f q = 0 := by
    intro q hq
    by_contra h
    have := hmax q (by simp [h])
    simp only at this
    omega
  have hab0 : f (a, b) ≠ 0 := by simpa using hpP
  have hval := noncompact_arr_one_values hF
  have hne : ε a ≠ ε b := fun h => hab0 ((hval a b).2 h)
  have hab : a ≠ b := fun h => hne (h ▸ rfl)
  refine ⟨a, b, hne, ?_⟩
  have hwt : IsWeight E (μ - root a b) (f (a, b)) := by
    intro c
    have h1 := congrArg (fun G : Arr V n 1 => G (fun _ => (a, b))) (hFh.1 c)
    simp only at h1
    rw [arr_operator_one_apply, PiLp.smul_apply] at h1
    by_cases hac : a = c
    · subst hac
      have hbc : b ≠ a := Ne.symm hab
      simp only [if_true, if_neg hbc, sub_zero] at h1
      have : ((μ - root a b) a : ℝ) = μ a - 1 := by
        simp [root, Pi.single_apply, hbc]
      rw [this]
      push_cast
      rw [sub_smul, one_smul, ← h1]
      simp [hf]
    · by_cases hbc : b = c
      · subst hbc
        simp only [if_neg hac, if_true, zero_sub] at h1
        have : ((μ - root a b) b : ℝ) = μ b + 1 := by
          simp [root, Pi.single_apply, hab]
        rw [this]
        push_cast
        rw [add_smul, one_smul, ← h1]
        simp [hf]
      · simp only [if_neg hac, if_neg hbc, sub_zero, zero_add] at h1
        have : ((μ - root a b) c : ℝ) = μ c := by
          simp [root, Pi.single_apply, Ne.symm hac, Ne.symm hbc]
        rw [this]
        exact h1
  have hhi : ∀ c d, c < d → ε c = ε d → E c d (f (a, b)) = 0 := by
    intro c d hcd hcomp
    have hcd' := Fin.lt_iff_val_lt_val.mp hcd
    have h1 := congrArg (fun G : Arr V n 1 => G (fun _ => (a, b))) (hFh.2 c d hcd hcomp)
    simp only at h1
    rw [arr_operator_one_apply, PiLp.zero_apply] at h1
    have e1 : (if a = c then F (fun _ => (d, b)) else 0) = 0 := by
      split_ifs with h
      · subst h
        exact hzero (d, b) (by simp only; omega)
      · rfl
    have e2 : (if b = d then F (fun _ => (a, c)) else 0) = 0 := by
      split_ifs with h
      · subst h
        exact hzero (a, c) (by simp only; omega)
      · rfl
    rw [e1, e2, sub_zero, zero_add] at h1
    exact h1
  have hν := compact_highest_weight_unique hl hw hg hu hΛ ((hval a b).1 hne) ⟨hwt, hhi⟩ hab0
  rw [← hν]
  simp
end Formalism.REAL
