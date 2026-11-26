-- Prove2me | solution 1 for Eden.isGreatest_selected_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:52.042577+00:00
-- url     : https://prove2.me/submissions/3999ae59-f52f-4029-a717-a88fd641a3d4

import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_SelectedProducts
import Theorems.Thm_Eden_prod_antitone_embedding_le
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_exists_equiv_of_multiset_eq
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
theorem _root_.solution {k n : ℕ} (hk : k ≤ n) {a b : Fin n → ℝ}
    (ha : Antitone a) (hpos : ∀ i, 0 ≤ a i)
    (hm : Finset.univ.val.map a = Finset.univ.val.map b) :
    IsGreatest {r : ℝ | ∃ s : Set.powersetCard (Fin n) k, r = ∏ j ∈ s.val, b j}
      (∏ i : Fin k, a (Fin.castLE hk i)) := by
  classical
  obtain ⟨e, he⟩ := exists_equiv_of_multiset_eq hm
  constructor
  · let f : Fin k ↪ Fin n := (Fin.castLEEmb hk).trans e.toEmbedding
    let s := Finset.univ.image f
    have hs : s.card = k := by simp [s, Finset.card_image_of_injective _ f.injective]
    refine ⟨⟨s, hs⟩, ?_⟩
    change (∏ i : Fin k, a (Fin.castLE hk i)) = ∏ j ∈ s, b j
    simp [s, Finset.prod_image, f.injective.injOn, f, he]
  · rintro r ⟨s, rfl⟩
    let f : Fin k ↪ Fin n := (Set.powersetCard.ofFinEmbEquiv.symm s).toEmbedding
    have hprod : (∏ j ∈ s.val, b j) = ∏ i : Fin k, b (f i) := by
      change (∏ j ∈ s.val, b j) = ∏ i : Fin k, b (s.val.orderEmbOfFin s.property i)
      conv_lhs => rw [← Finset.image_orderEmbOfFin_univ s.val s.property]
      rw [Finset.prod_image (fun _ _ _ _ h => (s.val.orderEmbOfFin s.property).injective h)]
    rw [hprod]
    have he' (j : Fin n) : b j = a (e.symm j) := by simpa using he (e.symm j)
    simp_rw [he']
    exact prod_antitone_embedding_le hk ha hpos (f.trans e.symm.toEmbedding)
end Eden
