-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.Eh_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:42.147801+00:00
-- url     : https://prove2.me/submissions/2de2c45d-ad8f-448f-befc-1ca956da8f28

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_Ee_comp_Tt
import Theorems.Thm_Formalism_FT_SymmetricSeries_Tt_Tt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable (R : Type*) [CommRing R] (n : ℕ)
variable {R n}
variable (R n)
variable {R n}
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution (p : MvPolynomial (Fin n) R) (hp : p.IsSymmetric) : ∃ q, Eh R n q = p := by
  obtain ⟨q, hq⟩ := MvPolynomial.esymmAlgHom_fin_surjective R (le_refl n)
    (⟨p, (MvPolynomial.mem_symmetricSubalgebra p).mpr hp⟩ : MvPolynomial.symmetricSubalgebra (Fin n) R)
  refine ⟨Tt R n q, ?_⟩
  have e1 : ∀ x, Ee R n (Tt R n x) = Eh R n x := fun x => by rw [← AlgHom.comp_apply, Ee_comp_Tt]
  rw [← e1, Tt_Tt]
  have h1 := congrArg Subtype.val hq
  rw [MvPolynomial.esymmAlgHom_apply] at h1
  exact h1
end Formalism.FT.SymmetricSeries
