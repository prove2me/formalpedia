-- Prove2me | solution 1 for BandParity.quartic_eq_or_eq_pow_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:26.908831+00:00
-- url     : https://prove2.me/submissions/6590027e-d413-442a-bc29-04c26caf566f

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_Pin
public import Theorems.Thm_BandParity_quartic_ext
public import Theorems.Thm_BandParity_pow_three_apply_of_pm_gi
public import Theorems.Thm_BandParity_exists_generator
public import Theorems.Thm_BandParity_quartic_apply_generator


set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution {χ ψ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) (hψ : orderOf ψ = 4) : ψ = χ ∨ ψ = χ ^ 3 := by
  obtain ⟨g, -, hg⟩ := exists_generator (p := p)
  have hc := quartic_apply_generator χ hχ hg
  have h3 := pow_three_apply_of_pm_gi χ hc
  rcases hc with hc | hc <;> rcases quartic_apply_generator ψ hψ hg with hs | hs
  · exact Or.inl (quartic_ext hg (by rw [hc, hs]))
  · exact Or.inr (quartic_ext hg (by rw [h3, hc, hs]))
  · exact Or.inr (quartic_ext hg (by rw [h3, hc, hs, neg_neg]))
  · exact Or.inl (quartic_ext hg (by rw [hc, hs]))
end BandParity
