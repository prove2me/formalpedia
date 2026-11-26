-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.binomialAnnulus_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:55.407892+00:00
-- url     : https://prove2.me/submissions/0bee788f-a027-4bb6-8ac6-0323387b37f4

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialAnnulusCode_injective

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 200000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (H j : ℕ) :
    (binomialAnnulus H j).card ≤ 2 * binomialAnnulusWidth H := by
  classical
  let A := binomialAnnulus H j
  let W := binomialAnnulusWidth H
  let code := binomialAnnulusCode H
  let codes : Finset (Bool × ℕ) :=
    Finset.univ.product (Finset.Ico (j * W) ((j + 1) * W))
  have himage : A.image code ⊆ codes := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨k, hkA, rfl⟩ := hz
    have hkData :
        j * W ≤ binomialCenterDistance H k ∧
          binomialCenterDistance H k < (j + 1) * W := by
      simpa [A, W, binomialAnnulus] using (Finset.mem_filter.mp hkA).2
    change binomialAnnulusCode H k ∈
      Finset.univ.product (Finset.Ico (j * W) ((j + 1) * W))
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa [binomialAnnulusCode] using (Finset.mem_Ico.mpr hkData)
  have hcardImage : (A.image code).card = A.card := by
    exact Finset.card_image_of_injective A
      (binomialAnnulusCode_injective H)
  calc
    (binomialAnnulus H j).card = (A.image code).card := by
      simpa [A] using hcardImage.symm
    _ ≤ codes.card := Finset.card_le_card himage
    _ = 2 * W := by
      simp [codes, W, Nat.add_mul]
    _ = 2 * binomialAnnulusWidth H := rfl
end CollatzEndpointTransport.FixedTotal
