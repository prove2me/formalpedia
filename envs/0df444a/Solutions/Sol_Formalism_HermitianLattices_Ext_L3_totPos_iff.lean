-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.totPos_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:15:13.796276+00:00
-- url     : https://prove2.me/submissions/a32445cf-808b-4d5a-9b2a-e410a439014c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_isReal_embedding_cmF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable (K : Type) [Field K] [NumberField K] [StarRing K]
variable {K}
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (a : cmF K) :
    TotPos (a : K) ↔ ∀ φ : cmF K →+* ℝ, 0 < φ a := by
  constructor
  · intro h φ
    obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (K := K) (InfinitePlace.mk (Complex.ofRealHom.comp φ))
    have hr := isReal_embedding_cmF hK w.embedding
    have hw' : InfinitePlace.mk (w.embedding.comp (algebraMap (cmF K) K)) =
        InfinitePlace.mk (Complex.ofRealHom.comp φ) := by
      rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
      exact hw
    rw [InfinitePlace.mk_eq_iff] at hw'
    have e : w.embedding.comp (algebraMap (cmF K) K) = Complex.ofRealHom.comp φ := by
      rcases hw' with e | e
      · exact e
      · rwa [ComplexEmbedding.isReal_iff.1 hr] at e
    have h1 := h w.embedding
    have e2 : w.embedding (a : K) = (φ a : ℂ) := RingHom.congr_fun e a
    rw [e2, Complex.ofReal_re] at h1
    exact h1
  · intro h ψ
    have hr := isReal_embedding_cmF hK ψ
    have e : ((hr.embedding a : ℝ) : ℂ) = ψ (a : K) := hr.coe_embedding_apply a
    rw [← e, Complex.ofReal_re]
    exact h _
end Formalism.HermitianLattices.Ext.L3
