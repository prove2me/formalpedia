-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.inv_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:47.331892+00:00
-- url     : https://prove2.me/submissions/f4b619ce-1f53-4c99-8a26-39b0798a0232

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_isOpen
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_ex
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_inv_one_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution (h : Ctx K R ϖ) {Om : Set K} (hOm : IsCompact Om) (hu : ∀ z ∈ Om, IsUnit z) :
    ∃ b : ℕ, ∀ z ∈ Om, ∀ zi : K, z * zi = 1 → zi ∈ Pk R ϖ (-(b : ℤ)) := by
  obtain ⟨b, hb⟩ := hOm.elim_directed_cover
    (fun b : ℕ => {z : K | ∃ zi ∈ Pk R ϖ (-(b : ℤ)), z * zi = 1})
    (by
      intro b
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨zi, hzi, hz1⟩
      have hU : {z' : K | z' - z ∈ Pk R ϖ ((b : ℤ) + 1)} ∈ 𝓝 z := by
        have hc : Continuous fun q : K => q - z := continuous_id.sub continuous_const
        exact hc.continuousAt.preimage_mem_nhds
          ((Pk_isOpen h _).mem_nhds (by simp))
      refine Filter.mem_of_superset hU ?_
      intro z' hz'
      have h1 : zi * (z' - z) ∈ Pk R ϖ 1 := by
        have := Pk_mul hzi hz'
        convert this using 2; ring
      obtain ⟨v, hv, hv1⟩ := inv_one_add h h1
      refine ⟨zi * v, Pk_smul hzi hv, ?_⟩
      linear_combination hv1 + v * hz1)
    (by
      intro z hz
      obtain ⟨w, rfl⟩ := hu z hz
      obtain ⟨b, hb⟩ := Pk_ex h ((w⁻¹ : Kˣ) : K)
      exact Set.mem_iUnion.2 ⟨b, _, hb, by simp⟩)
    (by
      intro i j
      exact ⟨max i j,
        fun x ⟨zi, hzi, hx⟩ => ⟨zi, Pk_mono h.mem (by push_cast; omega) hzi, hx⟩,
        fun x ⟨zi, hzi, hx⟩ => ⟨zi, Pk_mono h.mem (by push_cast; omega) hzi, hx⟩⟩)
  refine ⟨b, fun z hz zi hzi => ?_⟩
  obtain ⟨zi', hzi', hz1⟩ := hb hz
  have : zi = zi' := by
    calc zi = zi * (z * zi') := by rw [hz1, mul_one]
      _ = (z * zi) * zi' := by ring
      _ = zi' := by rw [hzi, one_mul]
  rw [this]; exact hzi'
end Formalism.FourierDecayAlt.P.HenselRootsBounded
