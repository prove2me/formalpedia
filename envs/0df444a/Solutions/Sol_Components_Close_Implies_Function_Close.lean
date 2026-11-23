-- Prove2me | solution 1 for Components_Close_Implies_Function_Close
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:41:50.750736+00:00
-- url     : https://prove2.me/submissions/cce78b25-4a1e-4b43-8ff2-522a8a0049c1

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Theorems.Thm_reconstruct_func_in_code
import Theorems.Thm_reconstruction_from_components


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution
    (D : Finset F) (m : ℕ) (d : ℕ) (hm : m > 0)
    (f : F → F) (S : Finset F) (hS : S ⊆ D)
    (f_i : Fin m → (pow_domain D m → F))
    (h_fi_def : ∀ i, ∀ z : pow_domain D m, f_i i z = folding_component D m f i (z : F))
    (h_close : ∀ i : Fin m, ∃ u_i ∈ reedSolomon (pow_domain D m) (d / m),
      ∀ z : pow_domain S m,
        u_i ⟨z.val, pow_domain_subset hS z.2⟩ = f_i i ⟨z.val, pow_domain_subset hS z.2⟩) :
    ∃ u ∈ reedSolomon D d, ∀ x : S, u ⟨x.val, hS x.2⟩ = f x := by
  choose u hu hu' using h_close
  -- Extend each $u_i$ by zero to the entire field $F$.
  let u_ext : Fin m → F → F := fun i x ↦ if h : x ∈ pow_domain D m then u i ⟨x, h⟩ else 0
  -- Show that the reconstruction of $u_ext$ is in the code of $D$.
  have hu_reconstruct : (D : Set F).restrict (reconstruct_func m u_ext) ∈ reedSolomon D d := by
    apply reconstruct_func_in_code
    intro i
    have h_eq : (↑(pow_domain D m) : Set F).restrict (u_ext i) = u i := by
      ext z; exact dif_pos z.2
    rw [h_eq]; exact hu i
  -- Show that the reconstruction of $u_ext$ agrees with $f$ on $S$.
  have hu_agree : ∀ x ∈ S, f x = reconstruct_func m u_ext x := by
    intro x hx
    simp only [reconstruct_func, u_ext]
    split_ifs with h
    · simp_all [pow_domain]
      simp only [hu' _ _ _ hx rfl, h_fi_def _ _ _ (hS hx) rfl,
        reconstruction_from_components D m hm f x (hS hx)]
    · grind [pow_domain]
  exact ⟨_, hu_reconstruct, fun x ↦ (hu_agree _ x.2).symm⟩
