-- Prove2me | solution 1 for BandParity.matching_indep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:14:24.199607+00:00
-- url     : https://prove2.me/submissions/9f0d5113-4cb4-477d-aa11-dee217f40b6e

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
public import Theorems.Thm_P2M_BandParity_matching_indep__280075205c52


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
namespace BandParity
theorem _root_.solution {ι κ : Type*} (X : Finset ι) (Y : Finset κ) (π π' : ι → κ)
    (hπ : Set.BijOn π X Y) (hπ' : Set.BijOn π' X Y) (σ : ι → ℤ) (τ : κ → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ y ∈ Y, τ y = 1 ∨ τ y = -1) :
    ∑ x ∈ X, σ x * τ (π x) ≡ ∑ x ∈ X, σ x * τ (π' x) [ZMOD 4] :=
  matching_indep' X Y π π' hπ hπ' σ τ hσ hτ
end BandParity
