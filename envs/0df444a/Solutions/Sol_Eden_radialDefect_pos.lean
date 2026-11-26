-- Prove2me | solution 1 for Eden.radialDefect_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:26.533817+00:00
-- url     : https://prove2.me/submissions/ae7e4c49-3ea6-4f33-b394-1f62654e1e45

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
import Theorems.Thm_Eden_continuousOn_squaredRadiusEvolution_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_strictMono_squaredRadiusEvolution
attribute [local simp] Eden.squaredRadiusEvolution_at_one


section
noncomputable section
open Set
namespace Eden
private theorem defect_intervalIntegrable {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    IntervalIntegrable (fun τ => (squaredRadiusEvolution τ s - 1) ^ 2)
      MeasureTheory.volume 0 t := by
  have hc := (((continuousOn_squaredRadiusEvolution_time s).mono
    (show Icc 0 t ⊆ Ici 0 from fun _ h => h.1)).sub
      (continuousOn_const (c := (1 : ℝ)))).pow 2
  exact hc.intervalIntegrable_of_Icc ht
end Eden
end
end

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 < t) (hs : s ≠ 1) :
    0 < radialDefect t s := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (defect_intervalIntegrable ht.le s)
    (fun τ hτ => ?_) ht
  apply sq_pos_of_ne_zero
  apply sub_ne_zero.mpr
  intro heq
  have hinj := (strictMono_squaredRadiusEvolution hτ.1.le).injective
  exact hs (hinj (heq.trans (squaredRadiusEvolution_at_one τ).symm))
end Eden
