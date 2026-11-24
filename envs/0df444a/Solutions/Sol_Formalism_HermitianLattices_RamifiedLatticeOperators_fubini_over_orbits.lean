-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.fubini_over_orbits
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:34.195351+00:00
-- url     : https://prove2.me/submissions/30ad31da-0a28-49fa-b2a5-081305310258

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.OneDimInversion
open Finset Formalism.LogVandermondeBounds.product_first_zeroth_parts
section T1
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {R : Type} [CommRing R]
end T1
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.LogVandermondeBounds.product_first_zeroth_parts Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.OneDimInversion
section Orb
private lemma natcard_stab_smul {Γ X : Type} [Group Γ] [MulAction Γ X] (g : Γ) (x : X) :
    Nat.card (MulAction.stabilizer Γ (g • x)) = Nat.card (MulAction.stabilizer Γ x) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective
private lemma count_fib {Γ P Q : Type} [Group Γ] [MulAction Γ P] [MulAction Γ Q] (pr : P → Q)
    (hpr : ∀ (γ : Γ) (p : P), pr (γ • p) = γ • pr p) (T : Finset P) (y : Q) (s : P)
    (hT : ∀ p, p ∈ T ↔ pr p = y ∧ p ∈ MulAction.orbit Γ s) (hs : pr s = y) :
    T.card * Nat.card (MulAction.stabilizer Γ s) = Nat.card (MulAction.stabilizer Γ y) := by
  classical
  have hle : MulAction.stabilizer Γ s ≤ MulAction.stabilizer Γ y := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [← hs, ← hpr, hg]
  set H := MulAction.stabilizer Γ y with hH
  have horb : (T : Set P) = MulAction.orbit H s := by
    ext p
    simp only [Finset.mem_coe, hT, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨hp, g, rfl⟩
      have hg : g ∈ H := by
        rw [hH, MulAction.mem_stabilizer_iff]
        calc g • y = g • pr s := by rw [hs]
          _ = pr (g • s) := (hpr g s).symm
          _ = y := hp
      exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨h, rfl⟩
      refine ⟨?_, (h : Γ), rfl⟩
      show pr ((h : Γ) • s) = y
      rw [hpr, hs]
      exact h.2
  have hstab : MulAction.stabilizer H s = (MulAction.stabilizer Γ s).subgroupOf H := by
    ext h
    simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  have hcs : Nat.card (MulAction.stabilizer H s) = Nat.card (MulAction.stabilizer Γ s) := by
    rw [hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hcardT : T.card = (MulAction.orbit H s).ncard := by
    rw [← horb, Set.ncard_coe_finset]
  rw [hcardT, ← MulAction.index_stabilizer, ← hcs]
  exact Subgroup.index_mul_card _
end Orb
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
theorem _root_.solution : Fubini_orbits := by
  intro Γ P Q V _ _ _ _ _ pr fib Ψ RP RQ hpr hfib hΨ hfinQ hRP hRQ
  classical
  choose rep hrep using fun p => (hRP p).exists
  have hrep_iff : ∀ p r, r ∈ RP → (rep p = r ↔ r ∈ MulAction.orbit Γ p) := by
    intro p r hr
    constructor
    · rintro rfl
      exact (hrep p).2
    · intro h
      exact (hRP p).unique (hrep p) ⟨hr, h⟩
  choose repQ hrepQ using fun y => (hRQ y).exists

  have hinner : ∀ y, ∑ p ∈ fib y, Ψ p =
      ∑ r ∈ RP, (((fib y).filter (fun p => rep p = r)).card : ℚ) • Ψ r := by
    intro y
    rw [← Finset.sum_fiberwise_of_maps_to (g := rep) (t := RP) (fun p _ => (hrep p).1)]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => Ψ r), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨γ, hγ⟩ := (hrep p).2
    rw [← hp.2, ← hγ, hΨ]

  have hweight : ∀ r ∈ RP, ∑ y ∈ RQ, ((Nat.card (MulAction.stabilizer Γ y) : ℚ))⁻¹ *
      (((fib y).filter (fun p => rep p = r)).card : ℚ) =
      ((Nat.card (MulAction.stabilizer Γ r) : ℚ))⁻¹ := by
    intro r hr
    obtain ⟨hy0, g, hg⟩ := hrepQ (pr r)
    set y0 := repQ (pr r) with hy0def
    rw [Finset.sum_eq_single y0]
    · set s := g • r with hsdef
      have hs : pr s = y0 := by rw [hsdef, hpr]; exact hg
      have hT : ∀ p, p ∈ (fib y0).filter (fun p => rep p = r) ↔
          pr p = y0 ∧ p ∈ MulAction.orbit Γ s := by
        intro p
        rw [Finset.mem_filter, hfib, hrep_iff p r hr]
        refine and_congr Iff.rfl ?_
        rw [MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
        constructor
        · rintro ⟨γ, hγ⟩
          refine ⟨γ⁻¹ * g⁻¹, ?_⟩
          rw [hsdef, smul_smul, mul_assoc, inv_mul_cancel, mul_one, ← hγ, inv_smul_smul]
        · rintro ⟨γ, hγ⟩
          refine ⟨g⁻¹ * γ⁻¹, ?_⟩
          rw [← hγ, hsdef, mul_smul, inv_smul_smul, inv_smul_smul]
      have hc := count_fib pr hpr _ y0 s hT hs
      rw [hsdef, natcard_stab_smul] at hc
      have hpos : 0 < Nat.card (MulAction.stabilizer Γ y0) := by
        haveI := hfinQ y0
        exact Nat.card_pos
      have hcq : ((Nat.card (MulAction.stabilizer Γ y0) : ℕ) : ℚ) =
          (((fib y0).filter (fun p => rep p = r)).card : ℚ) *
            (Nat.card (MulAction.stabilizer Γ r) : ℚ) := by
        rw [← hc]; push_cast; ring
      have hne : ((Nat.card (MulAction.stabilizer Γ y0) : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast hpos.ne'
      rw [hcq] at hne ⊢
      have h1 : (((fib y0).filter (fun p => rep p = r)).card : ℚ) ≠ 0 := left_ne_zero_of_mul hne
      have h2 : (Nat.card (MulAction.stabilizer Γ r) : ℚ) ≠ 0 := right_ne_zero_of_mul hne
      field_simp
    · intro y hy hne
      rw [mul_eq_zero]
      right
      rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp hpr'
      apply hne
      rw [hfib] at hp
      obtain ⟨γ, hγ⟩ := (hrep_iff p r hr).1 hpr'
      apply (hRQ (pr r)).unique ⟨hy, γ⁻¹, ?_⟩ ⟨hy0, g, hg⟩
      rw [← hγ, hpr, hp]
      exact inv_smul_smul γ y
    · intro h
      exact absurd hy0 h

  simp_rw [hinner, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [← Finset.sum_smul, hweight r hr]
end Formalism.HermitianLattices.RamifiedLatticeOperators
