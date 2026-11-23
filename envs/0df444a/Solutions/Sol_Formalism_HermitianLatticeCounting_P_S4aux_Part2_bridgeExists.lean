-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.bridgeExists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:39.34744+00:00
-- url     : https://prove2.me/submissions/05ff0e73-32a0-4ba6-8faf-a24f9bfd5bf9

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution : BridgeExists := by
  intro E _ _ V _ _ h O abelian₂ hO hL hI
  let iS : StarRing O :=
    { star := fun a => ⟨star a.1, hO a.1 a.2⟩
      star_involutive := fun a => Subtype.ext (star_star a.1)
      star_mul := fun a b => Subtype.ext (star_mul a.1 b.1)
      star_add := fun a b => Subtype.ext (star_add a.1 b.1) }
  let iM : Module O abelian₂ :=
    { smul := fun a v => ⟨a.1 • v.1, hL a.1 a.2 v.1 v.2⟩
      one_smul := fun v => Subtype.ext (one_smul E v.1)
      mul_smul := fun a b v => Subtype.ext (mul_smul a.1 b.1 v.1)
      smul_zero := fun a => Subtype.ext (smul_zero a.1)
      smul_add := fun a v w => Subtype.ext (smul_add a.1 v.1 w.1)
      add_smul := fun a b v => Subtype.ext (add_smul a.1 b.1 v.1)
      zero_smul := fun v => Subtype.ext (zero_smul E v.1) }
  let h' : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O :=
    LinearMap.mk₂'ₛₗ (RingHom.id O) (starRingEnd O) (fun v w => ⟨h v.1 w.1, hI v.1 v.2 w.1 w.2⟩)
      (fun a b c => Subtype.ext (by simp))
      (fun c a b => Subtype.ext (by
        show h (c.1 • a.1) b.1 = c.1 * h a.1 b.1
        simp))
      (fun a b c => Subtype.ext (by simp))
      (fun c a b => Subtype.ext (by
        show h a.1 (c.1 • b.1) = star c.1 * h a.1 b.1
        simp [starRingEnd_apply]))
  refine ⟨O, inferInstance, iS, abelian₂, inferInstance, iM, h', O.subtype, abelian₂.subtype, ?_⟩
  exact
    { io_inj := Subtype.coe_injective
      io_range := fun c => ⟨fun hc => ⟨⟨c, hc⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
      io_star := fun _ => rfl
      j_inj := Subtype.coe_injective
      j_range := fun v => ⟨fun hv => ⟨⟨v, hv⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
      j_smul := fun _ _ => rfl
      form := fun _ _ => rfl }
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
