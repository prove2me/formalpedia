-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.latticeEquivFun_map_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:04:28.931916+00:00
-- url     : https://prove2.me/submissions/a970df4e-52d6-4d82-9ba4-15b2ce1a12c5

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open UnitAddTorus
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_908
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)
namespace DedekindZeta.PoissonSummation
theorem _root_.solution :
    Measure.map (latticeEquivFun L b) volume
      = ENNReal.ofReal (ZLattice.covolume L) • (volume : Measure (Fin d → ℝ)) := by
  refine Measure.ext fun t ht => ?_
  rw [Measure.map_apply (latticeEquivFun L b).continuous.measurable ht,
    Measure.smul_apply, smul_eq_mul]
  -- Rewrite the preimage as the image under `Φ.symm`.
  have hpre : (latticeEquivFun L b) ⁻¹' t = (latticeEquivFun L b).symm '' t :=
    ((latticeEquivFun L b).image_symm_eq_preimage t).symm
  rw [hpre]
  -- `equivFun ∘ Φ.symm = id`, so the image formula applied to `Φ.symm '' t` gives back `t`.
  have hid : ((b.ofZLatticeBasis ℝ).equivFun ∘ ⇑(latticeEquivFun L b).symm) = id := by
    funext y
    show (latticeEquivFun L b) ((latticeEquivFun L b).symm y) = y
    exact (latticeEquivFun L b).apply_symm_apply y
  have himg : (b.ofZLatticeBasis ℝ).equivFun '' ((latticeEquivFun L b).symm '' t) = t := by
    rw [← Set.image_comp, hid, Set.image_id]
  have hmeas : MeasurableSet ((latticeEquivFun L b).symm '' t) := by
    rw [(latticeEquivFun L b).image_symm_eq_preimage]
    exact ht.preimage (latticeEquivFun L b).continuous.measurable
  have hvol := ZLattice.volume_image_eq_volume_div_covolume' L b
    (s := (latticeEquivFun L b).symm '' t) hmeas.nullMeasurableSet
  rw [himg] at hvol
  have ha : ENNReal.ofReal (ZLattice.covolume L) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (ZLattice.covolume_pos L volume)).ne'
  have ha' : ENNReal.ofReal (ZLattice.covolume L) ≠ ⊤ := ENNReal.ofReal_ne_top
  exact ((ENNReal.eq_div_iff ha ha').1 hvol).symm
end DedekindZeta.PoissonSummation
