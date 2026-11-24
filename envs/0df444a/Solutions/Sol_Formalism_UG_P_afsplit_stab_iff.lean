-- Prove2me | solution 1 for Formalism.UG.P.afsplit_stab_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:55:19.410829+00:00
-- url     : https://prove2.me/submissions/ebda8d4d-bbcc-4e4f-9b12-bf0a7fbae553

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Theorems.Thm_Formalism_UG_P_afsplit_mem_stdLat
import Theorems.Thm_Formalism_UG_P_afsplit_mulVec_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (S : Subring A) (g : GL n A) :
    g ∈ stabGL (stdLat (n := n) (A := A) S) ↔
      (∀ i j, (g : Matrix n n A) i j ∈ S) ∧ (∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ S) := by
  have hmem := fun x : n → A => afsplit_mem_stdLat (n := n) S x
  have hinv : ∀ x : n → A, ((g⁻¹ : GL n A) : Matrix n n A) *ᵥ ((g : Matrix n n A) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv' : ∀ x : n → A, (g : Matrix n n A) *ᵥ (((g⁻¹ : GL n A) : Matrix n n A) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hsingle : ∀ j : n, (Pi.single j (1 : A) : n → A) ∈ stdLat (n := n) (A := A) S := by
    intro j
    rw [hmem]
    intro i
    by_cases h : i = j
    · subst h
      simp
    · rw [Pi.single_eq_of_ne h]
      exact S.zero_mem
  have hcol : ∀ (M : Matrix n n A) (i j : n), (M *ᵥ Pi.single j (1 : A)) i = M i j := by
    intro M i j
    first
      | simp [Matrix.mulVec_single_one]
      | simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      | simp [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply]
  constructor
  · intro hg
    have hg' : ∀ x : n → A, x ∈ stdLat (n := n) (A := A) S ↔
        (g : Matrix n n A) *ᵥ x ∈ stdLat (n := n) (A := A) S := hg
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · have h1 := ((hmem _).mp ((hg' _).mp (hsingle j))) i
      rwa [hcol] at h1
    · have h1 : (g : Matrix n n A) *ᵥ (((g⁻¹ : GL n A) : Matrix n n A) *ᵥ Pi.single j 1) ∈
          stdLat (n := n) (A := A) S := by
        rw [hinv']
        exact hsingle j
      have h2 := ((hmem _).mp ((hg' _).mpr h1)) i
      rwa [hcol] at h2
  · rintro ⟨h1, h2⟩
    show ∀ x : n → A, x ∈ stdLat (n := n) (A := A) S ↔
      (g : Matrix n n A) *ᵥ x ∈ stdLat (n := n) (A := A) S
    intro x
    rw [hmem, hmem]
    constructor
    · intro hx i
      exact afsplit_mulVec_mem S _ h1 x hx i
    · intro hx i
      have h3 := afsplit_mulVec_mem S _ h2 _ hx i
      rwa [hinv] at h3
end Formalism.UG.P
