-- Prove2me | solution 1 for Formalism.FN.LowerVolumeBound.covol_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:29.10977+00:00
-- url     : https://prove2.me/submissions/18277973-c2ac-4242-ae91-96537c1114d5

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MinkowskiIILowerOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set ZSpan
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN Formalism.FN.LowerVolumeBound
namespace Formalism.FN.LowerVolumeBound
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (bv : Basis (Fin (finrank ℝ E)) ℝ E) (hv : ∀ i, bv i ∈ L) :
    ZLattice.covolume L μ ≤ μ.real (parallelepiped bv) := by
  classical
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ L) = Fintype.card (Fin (finrank ℝ E)) := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L, Fintype.card_fin]
  let bz : Basis (Fin (finrank ℝ E)) ℤ L :=
    (Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq hcard)
  let b' : Basis (Fin (finrank ℝ E)) ℝ E := bz.ofZLatticeBasis ℝ L
  have hb' : ((↑) : L → E) ∘ bz = ⇑b' := by
    funext i; simp [b']
  have hk : ∃ k : ℤ, b'.det bv = k := by
    refine ⟨(Matrix.of fun i j => bz.repr ⟨bv j, hv j⟩ i).det, ?_⟩
    rw [Basis.det_apply, Int.cast_det]
    congr 1
    ext i j
    rw [Basis.toMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact bz.ofZLatticeBasis_repr_apply ℝ L ⟨bv j, hv j⟩ i
  obtain ⟨k, hk⟩ := hk
  have hprod : bv.det b' * b'.det bv = 1 := by
    rw [Basis.det_mul_det, Basis.det_self]
  have hk0 : k ≠ 0 := by
    rintro rfl; simp [hk] at hprod
  have hdet : |bv.det b'| ≤ 1 := by
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
    have h2 : |bv.det b'| * |(k : ℝ)| = 1 := by rw [← abs_mul, ← hk, hprod, abs_one]
    nlinarith [abs_nonneg (bv.det b')]
  rw [ZLattice.covolume_eq_det_mul_measureReal L μ bz bv, hb',
    measureReal_congr (fundamentalDomain_ae_parallelepiped bv μ)]
  calc |bv.det b'| * μ.real (parallelepiped bv) ≤ 1 * μ.real (parallelepiped bv) := by
        gcongr
    _ = μ.real (parallelepiped bv) := one_mul _
end Formalism.FN.LowerVolumeBound
