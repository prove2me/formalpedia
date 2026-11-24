-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.top_level_pointwise_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:08:40.884359+00:00
-- url     : https://prove2.me/submissions/abdb0f52-92aa-4790-83b5-419755ccb67f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_TopLevelPointwiseIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (hCap : CapelliIdentityEntry) (hRTA : RightTypeAction) [FiniteDimensional ℂ Wq]
    (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' (Fin.last r) D)
    (hπ'r : IsCRepOn (UWset k r z') π') (hπ'c : ContinuousOn π' (UWset k r z'))
    {F : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ FFl k r z z' π π' (Fin.last r) D)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hGG : GGl k r z z' g ≠ 0)
    (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ) (hBs : IsFrameOf k r [g⁻¹ *ᵥ z, z'] Bs) (Y : ℂ) (v : Wq) :
    tL k r z z' (Fin.last r) Y 1 1 F g v = (GGl k r z z' g : ℂ) • F g (capRep k r π' Bs (Y + ((k : ℂ) - 2) / 2) v) := by
  have hBs' : IsFrameOf k r [z'] Bs :=
    ⟨hBs.1, hBs.2.1, fun a w hw => hBs.2.2 a w (List.mem_cons_of_mem _ hw)⟩
  rw [hCap _ k r z z' D F hz hz' hD.1 hF.1 g hg hGG Bs hBs Y, _root_.smul_apply,
    hRTA Wp Wq k r (k - 1) z z' π π' D hz hz' hD hπ'r hπ'c F hF g hg Bs hBs']
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
