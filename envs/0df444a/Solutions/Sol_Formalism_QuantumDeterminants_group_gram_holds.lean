-- Prove2me | solution 1 for Formalism.QuantumDeterminants.group_gram_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:56:41.702094+00:00
-- url     : https://prove2.me/submissions/a3673346-5a84-4be4-aa5e-25f03f40d605

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
import Theorems.Thm_Formalism_QuantumDeterminants_ggDet_keyM
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_swap
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_unitary
import Theorems.Thm_Formalism_QuantumDeterminants_ggBlockA
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
theorem _root_.solution : GGram := by
  intro k r z z' hz hz' g hg
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hM : gramM k r z z' g = fromBlocks (herm (Hpk k r) z z • ggLastU r) (Zhat k r z z' g)
      (Zhat k r z z' g)ᴴ (herm (Hpk k r) z' z' • ggLastU r) := by
    ext (a|a) (b|b)
    · exact ggBlockA k r z hz a b
    · rfl
    · show herm (Hpk k r) (fvec k r z b) (g *ᵥ fvec k r z' a) = star (Zhat k r z z' g b a)
      rw [ggHerm_swap _ (GBasic.Hpk_herm k r)]
      rfl
    · show herm (Hpk k r) (g *ᵥ fvec k r z' b) (g *ᵥ fvec k r z' a) = _
      rw [ggHerm_unitary _ _ hg']
      exact ggBlockA k r z' hz' a b
  have hreal : ∀ w : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) w w = ((-(Tz k r w) : ℝ) : ℂ) := by
    intro w
    have hc : star (herm (Hpk k r) w w) = herm (Hpk k r) w w :=
      (ggHerm_swap _ (GBasic.Hpk_herm k r) w w).symm
    have h1 : ((herm (Hpk k r) w w).re : ℂ) = herm (Hpk k r) w w := Complex.conj_eq_iff_re.1 hc
    rw [← h1, Tz, neg_neg]
  have hD1 : Dmin k r z z' g (Fin.last (r + 1)) = (Zhat k r z z' g).det := rfl
  have hD0 : Dmin k r z z' g ⟨r, by omega⟩ =
      ((Zhat k r z z' g).submatrix Fin.castSucc Fin.castSucc).det := rfl
  rw [hM, ggDet_keyM, det_conjTranspose, ← conjTranspose_submatrix, det_conjTranspose, ← mul_assoc,
    ← pow_add, Even.neg_one_pow ⟨r + 1, rfl⟩, one_mul, hreal z, hreal z']
  unfold Gf
  rw [hD1, hD0, Complex.star_def, Complex.mul_conj]
  have hc := Complex.mul_conj (((Zhat k r z z' g).submatrix Fin.castSucc Fin.castSucc).det)
  push_cast
  linear_combination ((Tz k r z : ℂ) * (Tz k r z' : ℂ)) * hc
end Formalism.QuantumDeterminants
