-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2x3_cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:39:34.623816+00:00
-- url     : https://prove2.me/submissions/45e73f8f-2bfe-4584-b54c-cbea2f8b0542

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (U : Submodule ℂ (Fin n → ℂ))
    (hpos : ∀ v ∈ U, v ≠ 0 → 0 < (herm H v v).re) (a b : Fin n → ℂ) (ha : a ∈ U) (hb : b ∈ U) :
    Complex.normSq (herm H a b) ≤ (herm H a a).re * (herm H b b).re := by
  have hnn : ∀ v ∈ U, 0 ≤ (herm H v v).re := by
    intro v hv
    by_cases h0 : v = 0
    · subst h0; simp [herm]
    · exact le_of_lt (hpos v hv h0)
  have hreal : ∀ v, (herm H v v).im = 0 := by
    intro v
    have := ggHerm_swap H hH v v
    have h2 := congrArg Complex.im this
    simp only [Complex.star_def, Complex.conj_im] at h2
    linarith
  by_cases hb0 : b = 0
  · subst hb0; simp [herm]
  have hbpos := hpos b hb hb0
  set β := herm H a b with hβ
  set q : ℝ := (herm H b b).re with hq
  have hbb : herm H b b = (q : ℂ) := Complex.ext rfl (by rw [hreal]; simp)
  have hba : herm H b a = conj β := by rw [ggHerm_swap H hH b a]; rfl
  set s : ℂ := β / (q : ℂ) with hs
  have hx : a - s • b ∈ U := U.sub_mem ha (U.smul_mem s hb)
  have hexp : herm H (a - s • b) (a - s • b) =
      herm H a a - conj s * β - s * herm H b a + s * conj s * herm H b b := by
    simp only [herm, Matrix.mulVec_sub, Matrix.mulVec_smul, star_sub, star_smul, dotProduct_sub,
      sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, hβ]
    simp only [Complex.star_def]
    ring
  have hqne : (q : ℂ) ≠ 0 := by exact_mod_cast hbpos.ne'
  have hkey : herm H (a - s • b) (a - s • b) = herm H a a - ((Complex.normSq β / q : ℝ) : ℂ) := by
    rw [hexp, hba, hbb, hs]
    have hn : ((Complex.normSq β : ℝ) : ℂ) = conj β * β := Complex.normSq_eq_conj_mul_self
    rw [map_div₀, Complex.conj_ofReal]
    push_cast
    rw [hn]
    field_simp
    ring
  have h1 := hnn _ hx
  rw [hkey, Complex.sub_re, Complex.ofReal_re] at h1
  have : Complex.normSq β / q ≤ (herm H a a).re := by linarith
  rw [div_le_iff₀ hbpos] at this
  linarith
end Formalism.FourierDecayAlt.P
