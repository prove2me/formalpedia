-- Prove2me | solution 1 for Formalism.NG.finPres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:09:34.775861+00:00
-- url     : https://prove2.me/submissions/06989324-ce8f-4b5e-81a0-819faf7650e4

import Definitions.Def_Formalism_CharacterColumnKernels_StatGlobalModule
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CupKillAdm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NG
open Module
namespace Formalism.NG
theorem _root_.solution : StatFinPres := by
  intro R _ _ M _ _ g₀ n hn
  classical
  let f : (Fin g₀ → R) →ₗ[R] M :=
    { toFun := fun c => ∑ i, c i • n i
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hn, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    simp [f, Pi.single_apply]
  obtain ⟨m, s, hs⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (LinearMap.ker f))
  refine ⟨m, Matrix.of s, ⟨?_⟩⟩
  have hrel : relSpan (Matrix.of s) = LinearMap.ker f := by
    rw [relSpan, ← hs]
    rfl
  exact ((Submodule.quotEquivOfEq _ _ hrel).trans (f.quotKerEquivOfSurjective hsurj)).symm
end Formalism.NG
