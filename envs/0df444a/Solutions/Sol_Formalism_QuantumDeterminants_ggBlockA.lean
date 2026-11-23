-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ggBlockA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:28.04607+00:00
-- url     : https://prove2.me/submissions/0a782b79-9fcf-4f37-9931-26455cc8c4ab

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
import Theorems.Thm_Formalism_QuantumDeterminants_ggHpk_mulVec_Wb
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_swap
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_bvec_right
import Theorems.Thm_Formalism_QuantumDeterminants_ggHpk_ee
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z b) (fvec k r z a) = (herm (Hpk k r) z z • ggLastU r) a b := by
  rw [Matrix.smul_apply, smul_eq_mul]
  have hza : ∀ c : Fin r, (Hpk k r *ᵥ z) (eI k r c) = 0 := by
    intro c
    rw [ggHpk_mulVec_Wb k r z hz, hz _ (Or.inl (by simp [eI])), mul_zero]
  unfold fvec ggLastU
  by_cases ha : a.val < r <;> by_cases hb : b.val < r
  · rw [dif_pos ha, dif_pos hb, if_neg (by intro h; have := congrArg Fin.val h.1; simp at this; omega)]
    simp only [bvec, ggHerm_bvec_right, mulVec_single_one]
    simp [ggHpk_ee]
  · rw [dif_pos ha, dif_neg hb, if_neg (by intro h; have := congrArg Fin.val h.1; simp at this; omega)]
    simp only [bvec, ggHerm_bvec_right, hza, mul_zero]
  · rw [dif_neg ha, dif_pos hb, if_neg (by intro h; have := congrArg Fin.val h.2; simp at this; omega)]
    rw [ggHerm_swap _ (GBasic.Hpk_herm k r), bvec, ggHerm_bvec_right, hza, star_zero, mul_zero]
  · have hal : a = Fin.last r := Fin.ext (by simp; omega)
    have hbl : b = Fin.last r := Fin.ext (by simp; omega)
    rw [dif_neg ha, dif_neg hb, if_pos ⟨hal, hbl⟩, mul_one]
end Formalism.QuantumDeterminants
