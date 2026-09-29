-- Prove2me | solution 1 for ExtCitation.exists_padicLevel_fixingSubgroup_eq_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/bb187194-46d2-54a2-9048-e8d25b328897

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum

import Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_exists_padicLevel_fixingSubgroup_eq_of_isOpen

set_option autoImplicit false
set_option maxHeartbeats 1600000
open ExtCitation

theorem solution (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S) :
    ∃ K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)), FiniteDimensional ℚ_[(q : ℕ)] K ∧
      (K.fixingSubgroup : Subgroup (primeLocalGaloisGroup q)) = S := by
  classical
  obtain ⟨F₀, hF₀, hFS⟩ := hS
  haveI := hF₀

  obtain ⟨E₁, hE₁, hE₁S⟩ := (exists_finiteDimensional_comap_localGaloisToGlobal_iff (q : ℕ)
    (fun V => (V : Subgroup (primeLocalGaloisGroup q)) ≤ S) (fun U V hVU hU => le_trans hVU hU)).1 ⟨F₀, hF₀, hFS⟩
  haveI := hE₁

  let E₀ : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)) := IntermediateField.normalClosure ℚ_[(q : ℕ)] E₁ (PadicAlgCl (q : ℕ))
  haveI : FiniteDimensional ℚ_[(q : ℕ)] E₀ := normalClosure.is_finiteDimensional ℚ_[(q : ℕ)] E₁ (PadicAlgCl (q : ℕ))
  haveI : Normal ℚ_[(q : ℕ)] E₀ := normalClosure.normal ℚ_[(q : ℕ)] E₁ (PadicAlgCl (q : ℕ))
  haveI : IsGalois ℚ_[(q : ℕ)] E₀ := ⟨⟩
  have hE₀S : (E₀.fixingSubgroup : Subgroup (primeLocalGaloisGroup q)) ≤ S :=
    le_trans (IntermediateField.fixingSubgroup_antitone (IntermediateField.le_normalClosure E₁)) hE₁S

  let res : (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ)) →* (E₀ ≃ₐ[ℚ_[(q : ℕ)]] E₀) := AlgEquiv.restrictNormalHom E₀
  have hres : Function.Surjective res := AlgEquiv.restrictNormalHom_surjective (PadicAlgCl (q : ℕ))
  have hkerres : res.ker = E₀.fixingSubgroup := IntermediateField.restrictNormalHom_ker E₀
  let SE : Subgroup (E₀ ≃ₐ[ℚ_[(q : ℕ)]] E₀) := Subgroup.map res (S : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ)))
  have hmemSE : ∀ σ, res σ ∈ SE ↔ σ ∈ S := by
    intro σ
    constructor
    · rintro ⟨τ, hτ, hτσ⟩
      have : τ⁻¹ * σ ∈ res.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hτσ, inv_mul_cancel]
      rw [hkerres] at this
      have h2 := hE₀S this
      have : σ = τ * (τ⁻¹ * σ) := by group
      rw [this]
      exact S.mul_mem hτ h2
    · intro hσ
      exact ⟨σ, hσ, rfl⟩

  let K' : IntermediateField ℚ_[(q : ℕ)] E₀ := IntermediateField.fixedField SE
  let K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)) := IntermediateField.lift K'
  let eK : K' ≃ₐ[ℚ_[(q : ℕ)]] K := IntermediateField.liftAlgEquiv K'
  refine ⟨K, LinearEquiv.finiteDimensional eK.toLinearEquiv, ?_⟩
  ext σ
  have key : σ ∈ K.fixingSubgroup ↔ res σ ∈ K'.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      apply Subtype.ext
      have hxK : (x : PadicAlgCl (q : ℕ)) ∈ K := (IntermediateField.mem_lift x).2 hx
      have := h x hxK
      rw [← this]
      exact AlgEquiv.restrictNormal_commutes σ E₀ x
    · rintro h _ ⟨x, hx, rfl⟩
      have := congrArg (fun y : E₀ => (y : PadicAlgCl (q : ℕ))) (h x hx)
      show σ (x : PadicAlgCl (q : ℕ)) = (x : PadicAlgCl (q : ℕ))
      exact (AlgEquiv.restrictNormal_commutes σ E₀ x).symm.trans this
  show σ ∈ K.fixingSubgroup ↔ σ ∈ S
  rw [key, IntermediateField.fixingSubgroup_fixedField SE, hmemSE]

end S_ExtCitation_exists_padicLevel_fixingSubgroup_eq_of_isOpen
end P2MW
export P2MW.S_ExtCitation_exists_padicLevel_fixingSubgroup_eq_of_isOpen (solution)
