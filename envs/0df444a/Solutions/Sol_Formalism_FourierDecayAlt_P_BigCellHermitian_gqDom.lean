-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:30:04.858803+00:00
-- url     : https://prove2.me/submissions/8645538b-e5b5-49dc-89ac-3c6e62eb8681

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellHermitian_herm_bigCell
import Theorems.Thm_Formalism_QuantumDeterminants_big_cell_mem_holds
import Theorems.Thm_Formalism_QuantumDeterminants_big_cell_minors_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellHermitian
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.TwoByOneBlock
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BigCellHermitian
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QDom k r D.z D.z') :
    gq D q ∈ Om k r D.z D.z' := by
  obtain ⟨hc, hζ⟩ := hq
  have hsec := D.sec.2 q.2 hζ
  have hmin := big_cell_minors_holds k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem
  refine ⟨big_cell_mem_holds k r q.1 _ hc hsec.1, ?_, ?_⟩
  · intro l hl
    have h := hmin.1 ⟨l.val, by omega⟩
    have hl' : (⟨(⟨l.val, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 2)) = l := Fin.ext rfl
    show Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) l ≠ 0
    rw [← hl', h]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  · have hz := hmin.2.2 hc
    rw [herm_bigCell _ _ D.z_mem D.z'_mem, hsec.2] at hz
    have hr := hmin.1 (Fin.last r)
    set P := Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) ⟨r, by omega⟩ with hP
    have hP0 : P ≠ 0 := by
      have : P = ∏ a : Fin r with a.val < (Fin.last r).val, q.1 a := hr
      rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
    have hlast : Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1)) = q.2 * P := by
      unfold zeta at hz
      rw [← hP] at hz
      have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1))) hP0
      rw [hz] at h2
      exact h2.symm
    show 0 < Gf k r D.z D.z' (gq D q)
    unfold Gf gq
    rw [hlast, ← hP, Complex.normSq_mul]
    have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
    nlinarith
end Formalism.FourierDecayAlt.P.BigCellHermitian
