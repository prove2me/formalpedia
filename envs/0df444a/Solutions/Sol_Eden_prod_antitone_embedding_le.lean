-- Prove2me | solution 1 for Eden.prod_antitone_embedding_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:44:50.872051+00:00
-- url     : https://prove2.me/submissions/c102ad2d-043d-4a02-b418-97921bc78e2f

import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_SelectedProducts
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_orderEmbedding_fin_val_le
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {k n : ℕ} (hk : k ≤ n) {a : Fin n → ℝ}
    (ha : Antitone a) (hpos : ∀ i, 0 ≤ a i) (e : Fin k ↪ Fin n) :
    (∏ i : Fin k, a (e i)) ≤ ∏ i : Fin k, a (Fin.castLE hk i) := by
  classical
  let s := Finset.univ.image e
  have hs : s.card = k := by simp [s, Finset.card_image_of_injective _ e.injective]
  let o := s.orderEmbOfFin hs
  have hprod : (∏ i : Fin k, a (e i)) = ∏ i : Fin k, a (o i) := by
    calc
      (∏ i : Fin k, a (e i)) = ∏ j ∈ s, a j := by
        simp [s, Finset.prod_image, e.injective.injOn]
      _ = ∏ i : Fin k, a (o i) := by
        rw [← Finset.image_orderEmbOfFin_univ s hs,
          Finset.prod_image (fun _ _ _ _ h => (s.orderEmbOfFin hs).injective h)]
  rw [hprod]
  exact Finset.prod_le_prod (fun i _ => hpos (o i))
    (fun i _ => ha (orderEmbedding_fin_val_le o i))
end Eden
