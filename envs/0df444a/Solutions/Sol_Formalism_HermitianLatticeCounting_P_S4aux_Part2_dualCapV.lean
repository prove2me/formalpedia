-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.dualCapV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:39.438983+00:00
-- url     : https://prove2.me/submissions/760b92c4-127b-4751-be55-cacc4121fd5e

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
theorem _root_.solution (H : DualCap) : DualCapV := by
  intro o O' Lam' _ _ _ _ _ _ _ _ _ _ h' E _ _ V _ _ h O abelian₂ io j hU hSD hM hunit hspan Z y hy
  let S' : Submodule O' Lam' :=
    { carrier := {v | j v ∈ Z}
      add_mem' := fun {a b} ha hb => by
        show j (a + b) ∈ Z
        rw [map_add]; exact Z.add_mem ha hb
      zero_mem' := by
        show j 0 ∈ Z
        rw [map_zero]; exact Z.zero_mem
      smul_mem' := fun a v hv => by
        show j (a • v) ∈ Z
        rw [hM.j_smul]; exact Z.smul_mem _ hv }
  have hsat : Satur o S' := by
    intro c v hc hmem
    have h1 : io (algebraMap o O' c) • j v ∈ Z := by rw [← hM.j_smul]; exact hmem
    obtain ⟨u, hu⟩ := hunit c hc
    have h2 : j v = ((u⁻¹ : Eˣ) : E) • (io (algebraMap o O' c) • j v) := by
      rw [← hu, smul_smul]; simp
    show j v ∈ Z
    rw [h2]; exact Z.smul_mem _ h1
  have hex : ∀ v : S', ∃ a, io a = h (j v) y := fun v =>
    (hM.io_range _).mp (hy (j v) ((hM.j_range _).mpr ⟨v, rfl⟩) v.2)
  choose F hF using hex
  let φ : S' →ₗ[O'] O' :=
    { toFun := F
      map_add' := fun a b => hM.io_inj (by
        rw [map_add, hF, hF, hF]; simp)
      map_smul' := fun c a => hM.io_inj (by
        rw [hF, RingHom.id_apply, smul_eq_mul, map_mul, hF]; simp [hM.j_smul]) }
  obtain ⟨w, hw⟩ := H o O' Lam' h' hU hSD S' hsat φ
  refine ⟨j w, (hM.j_range _).mpr ⟨w, rfl⟩, fun z hz => ?_⟩
  obtain ⟨c, hc, hcz⟩ := hspan z
  obtain ⟨v', hv'⟩ := (hM.j_range _).mp hcz
  have hv'S : v' ∈ S' := by
    show j v' ∈ Z
    rw [hv']; exact Z.smul_mem _ hz
  have h1 : h (j v') y = h (j v') (j w) := by
    have := hw ⟨v', hv'S⟩
    have h2 : io (F ⟨v', hv'S⟩) = io (h' v' w) := congrArg io this
    rw [hF, ← hM.form] at h2
    exact h2
  rw [hv'] at h1
  have h3 : io (algebraMap o O' c) * h z (y - j w) = 0 := by
    have : h (io (algebraMap o O' c) • z) (y - j w) = 0 := by rw [map_sub, h1, sub_self]
    simpa using this
  exact (hunit c hc).mul_right_eq_zero.mp h3
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
