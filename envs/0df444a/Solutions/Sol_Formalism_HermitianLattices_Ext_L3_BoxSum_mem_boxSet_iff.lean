-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.mem_boxSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:47.851838+00:00
-- url     : https://prove2.me/submissions/33637550-9121-4fae-be7f-dc0e73bb0775

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_rEmb_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_isTotallyReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F} :
    n ∈ boxSet K F T ↔ ∀ w : {w : InfinitePlace F // w.IsReal}, 0 < rEmb w n ∧ rEmb w n ≤ T := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  constructor
  · intro h w
    let _ : Algebra F ℂ := w.1.embedding.toAlgebra
    let φ : K →ₐ[F] ℂ := IsAlgClosed.lift
    have h1 : φ (algebraMap F K (n : F)) = w.1.embedding (n : F) := φ.commutes _
    have h2 := h φ.toRingHom
    have h3 : (φ.toRingHom (algebraMap F K (n : F))).re = rEmb w n := by
      show (φ (algebraMap F K (n : F))).re = _
      rw [h1, rEmb_apply, ← InfinitePlace.embedding_of_isReal_apply w.2, Complex.ofReal_re]
    rwa [h3] at h2
  · intro h φ
    have hw : (InfinitePlace.mk (φ.comp (algebraMap F K))).IsReal := IsTotallyReal.isReal _
    have h1 := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hw)
    have h3 : (φ (algebraMap F K (n : F))).re = rEmb ⟨_, hw⟩ n := by
      rw [rEmb_apply, ← Complex.ofReal_re (InfinitePlace.embedding_of_isReal _ _),
        InfinitePlace.embedding_of_isReal_apply hw, h1]
      rfl
    rw [h3]
    exact h _
end Formalism.HermitianLattices.Ext.L3.BoxSum
