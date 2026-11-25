-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.haarWb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:54.032302+00:00
-- url     : https://prove2.me/submissions/3ac8d655-1ca2-4f01-b063-82e54b7486e0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haar_push
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haar_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_uwb_iff
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x3_Jm__b_3f1be2078428
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_closedEmb
import Theorems.Thm_Formalism_REAL_uJEmb
import Theorems.Thm_Formalism_REAL_unimodular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution : HaarWbExists := by
  intro k r
  have : (muG (εb k)).IsMulRightInvariant := ⟨fun g => unimodular _ (εb k) g⟩
  have hemb := uJEmb _ (εb k)
  let ι : UJ (εb k) → (Fin (k + 1) → Fin (k + 1) → ℂ) :=
    fun g => ((g : (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ˣ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
  have hι : IsClosedEmbedding ι := hemb.1
  have hιr : ∀ x : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, inUJ (εb k) x ↔ ∃ g, ι g = x := fun x => by
    have := Set.ext_iff.mp hemb.2 x
    exact this.symm
  refine ⟨(muG (εb k)).map ((fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r)) ∘ ι), ?_⟩
  apply haar_push (muG (εb k)) (haar_ne_zero _) _ (emb_closedEmb.comp hι)
  · intro a b
    exact emb_mul _ _
  · ext g
    constructor
    · rintro ⟨x, rfl⟩
      apply (uwb_iff _).mpr
      refine ⟨Matrix.of (ι x), ?_, rfl⟩
      have := (hιr (Matrix.of (ι x))).mpr ⟨x, rfl⟩
      unfold inUJ at this
      rwa [Jm_εb] at this
    · intro hg
      obtain ⟨a, ha, hag⟩ := (uwb_iff _).mp hg
      have h2 : inUJ (εb k) a := by
        unfold inUJ
        rwa [Jm_εb]
      obtain ⟨x, hx⟩ := (hιr a).mp h2
      refine ⟨x, ?_⟩
      show embWb k r (Matrix.of (ι x)) = g
      rw [hx]
      exact hag
end Formalism.FourierDecayAlt.P.B2x3
