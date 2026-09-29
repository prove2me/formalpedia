-- Prove2me | solution 1 for DFT.external_energy_eq_density_pairing
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:38:07.873497+00:00
-- url     : https://prove2.me/submissions/2a261f01-1424-4a2c-a1c3-608edb4cdfcd

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory
open DFT

namespace Ag3Aux_ExtEnergy

theorem mp (n : ℕ) (i : Fin (n + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Pos) i)
      (volume : Measure (Config n)) ((volume : Measure Pos).prod (volume : Measure (Fin n → Pos))) :=
  volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Pos) i

theorem symm_apply (n : ℕ) (i : Fin (n + 1)) (p : Pos × (Fin n → Pos)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Pos) i).symm p = i.insertNth p.1 p.2 :=
  rfl

end Ag3Aux_ExtEnergy

open Ag3Aux_ExtEnergy

theorem solution {n : ℕ} (v : Pos → ℝ) (Ψ : Config n → ℂ)
    (hv : Measurable v) (hΨ : Measurable Ψ)
    (hint : ∀ i : Fin (n + 1), Integrable fun x : Config n => v (x i) * ‖Ψ x‖ ^ 2) :
    ∫ x : Config n, (∑ i, v (x i)) * ‖Ψ x‖ ^ 2 = ∫ r : Pos, v r * oneParticleDensity Ψ r := by
  set F : Fin (n + 1) → Pos × (Fin n → Pos) → ℝ :=
    fun i p => v p.1 * ‖Ψ (i.insertNth p.1 p.2)‖ ^ 2 with hFdef
  have hcomp : ∀ i, (fun x : Config n => v (x i) * ‖Ψ x‖ ^ 2) ∘
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Pos) i).symm = F i := by
    intro i; funext p
    simp only [Function.comp_apply, symm_apply, hFdef, Fin.insertNth_apply_same]
  have hF : ∀ i, Integrable (F i) ((volume : Measure Pos).prod (volume : Measure (Fin n → Pos))) := by
    intro i
    rw [← hcomp i, (mp n i).symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    exact hint i
  have hFi : ∀ i, ∫ x : Config n, v (x i) * ‖Ψ x‖ ^ 2
      = ∫ r : Pos, ∫ y : Fin n → Pos, F i (r, y) := by
    intro i
    rw [← integral_prod _ (hF i), ← (mp n i).symm.integral_comp' (fun x : Config n => v (x i) * ‖Ψ x‖ ^ 2)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun p => congrFun (hcomp i) p))
  have hL : ∫ x : Config n, (∑ i, v (x i)) * ‖Ψ x‖ ^ 2
      = ∑ i, ∫ x : Config n, v (x i) * ‖Ψ x‖ ^ 2 := by
    simp_rw [Finset.sum_mul]
    exact integral_finset_sum _ (fun i _ => hint i)
  have hR : ∀ r, v r * oneParticleDensity Ψ r = ∑ i, ∫ y : Fin n → Pos, F i (r, y) := by
    intro r
    simp only [oneParticleDensity, Finset.mul_sum, hFdef]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul]
  simp_rw [hR]
  rw [integral_finset_sum _ (fun i _ => (hF i).integral_prod_left), hL]
  exact Finset.sum_congr rfl (fun i _ => hFi i)
