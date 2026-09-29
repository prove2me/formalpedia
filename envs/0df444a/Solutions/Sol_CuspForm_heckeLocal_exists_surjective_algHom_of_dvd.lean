-- Prove2me | solution 1 for CuspForm.heckeLocal.exists_surjective_algHom_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6d27ba56-3706-5db8-a29a-d89d1f9e3e28

import Definitions.Def_CuspForm_HeckeLocal
import Theorems.Thm_CuspForm_heckeAlgebra_exists_surjective_ringHom_of_dvd
import Theorems.Thm_CuspForm_heckeLocal_exists_factor_algHom
import Theorems.Thm_CuspForm_heckeLocal_adjoin_range_pi
import Theorems.Thm_CuspForm_heckeLocal_residue_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_exists_surjective_algHom_of_dvd

set_option autoImplicit false

noncomputable section

namespace HresB

open CuspForm

variable {N N' : ℕ} [NeZero N] [NeZero N'] {S : Set ℕ}

set_option synthInstance.maxHeartbeats 800000 in

theorem ringHom_ext {A : Type} [Ring A] (hN'S : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S)
    (φ ψ : heckeAlgebra N' 2 S →+* A)
    (h : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN' : ¬ ℓ ∣ N') (hℓS : ℓ ∉ S),
      φ (heckeAlgebra.T hℓ hℓN' hℓS) = ψ (heckeAlgebra.T hℓ hℓN' hℓS)) :
    φ = ψ := by
  refine RingHom.ext fun t => ?_
  obtain ⟨t, ht⟩ := t
  refine Algebra.adjoin_induction (p := fun t ht => φ ⟨t, ht⟩ = ψ ⟨t, ht⟩) ?_ ?_ ?_ ?_ ht
  · rintro t (⟨ℓ, hℓ, hℓN', hℓS, rfl⟩ | ⟨q, hqN', hq, hqS, rfl⟩)
    · exact h ℓ hℓ hℓN' hℓS
    · exact absurd (hN'S q hq hqN') hqS
  · intro r
    have e : (⟨algebraMap ℤ _ r, algebraMap_mem _ r⟩ : heckeAlgebra N' 2 S) = (r : heckeAlgebra N' 2 S) :=
      Subtype.ext (by simp)
    rw [e, map_intCast φ r, map_intCast ψ r]
  · intro x y hx hy hpx hpy
    have ex : (⟨x + y, add_mem hx hy⟩ : heckeAlgebra N' 2 S) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [ex, φ.map_add, ψ.map_add, hpx, hpy]
  · intro x y hx hy hpx hpy
    have ex : (⟨x * y, mul_mem hx hy⟩ : heckeAlgebra N' 2 S) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [ex, φ.map_mul, ψ.map_mul, hpx, hpy]

end HresB

end

open CuspForm in
theorem solution
    (N N' : ℕ) [NeZero N] [NeZero N'] (hNN' : N ∣ N') (S : Set ℕ)
    (hN'S : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
    (θ' : CuspForm.heckeAlgebra N' 2 S →+* IsLocalRing.ResidueField 𝒪)
    (hθ' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN' : ¬ ℓ ∣ N') (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      θ' (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS) = θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))
    (hint : CuspForm.HasIntegralStructure N 2) (hint' : CuspForm.HasIntegralStructure N' 2) :
    ∃ (res : CuspForm.heckeAlgebra N' 2 S →+* CuspForm.heckeAlgebra N 2 S)
      (Ψ : CuspForm.heckeLocal N' S 𝒪 θ' →ₐ[𝒪] CuspForm.heckeLocal N S 𝒪 θ),
      θ' = θ.comp res ∧ Function.Surjective res ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN' : ¬ ℓ ∣ N') (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        res (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS) = CuspForm.heckeAlgebra.T hℓ hℓN hℓS) ∧
      IsLocalHom (Ψ : CuspForm.heckeLocal N' S 𝒪 θ' →+* CuspForm.heckeLocal N S 𝒪 θ) ∧
      Function.Surjective Ψ ∧
      ∀ t : CuspForm.heckeAlgebra N' 2 S,
        Ψ (CuspForm.heckeLocal.π N' S 𝒪 θ' t) = CuspForm.heckeLocal.π N S 𝒪 θ (res t) := by
  classical

  obtain ⟨res, hres_surj, hres_T, -⟩ :=
    CuspForm.heckeAlgebra.exists_surjective_ringHom_of_dvd N N' hNN' 2 S hN'S

  have hθres : θ' = θ.comp res := by
    refine HresB.ringHom_ext hN'S θ' (θ.comp res) fun ℓ hℓ hℓN' hℓS => ?_
    have hℓN : ¬ ℓ ∣ N := fun hd => hℓN' (hd.trans hNN')
    rw [RingHom.comp_apply, hres_T ℓ hℓ hℓN' hℓN hℓS, hθ' ℓ hℓ hℓN' hℓN hℓS]

  haveI : Fact (HasIntegralStructure N 2) := ⟨hint⟩
  set π' : heckeAlgebra N' 2 S →+* heckeLocal N S 𝒪 θ := (heckeLocal.π N S 𝒪 θ).comp res
    with hπ'def
  have hπ' : ∀ t, IsLocalRing.residue (heckeLocal N S 𝒪 θ) (π' t) =
      IsLocalRing.ResidueField.map (algebraMap 𝒪 (heckeLocal N S 𝒪 θ)) (θ' t) := by
    intro t
    rw [hπ'def, RingHom.comp_apply, CuspForm.heckeLocal.residue_pi N S 𝒪 θ (res t), hθres,
      RingHom.comp_apply]
  obtain ⟨Ψ, hΨloc, hΨπ⟩ :=
    CuspForm.heckeLocal.exists_factor_algHom N' S 𝒪 θ' hint' (heckeLocal N S 𝒪 θ) π' hπ'

  have hΨsurj : Function.Surjective Ψ := by
    have hle : Algebra.adjoin 𝒪 (Set.range (heckeLocal.π N S 𝒪 θ)) ≤ Ψ.range := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨s, rfl⟩
      obtain ⟨t, rfl⟩ := hres_surj s
      exact ⟨heckeLocal.π N' S 𝒪 θ' t, (hΨπ t).trans (by rw [hπ'def, RingHom.comp_apply])⟩
    rw [CuspForm.heckeLocal.adjoin_range_pi N S 𝒪 θ hint, top_le_iff] at hle
    intro y
    have hy : y ∈ Ψ.range := hle ▸ Algebra.mem_top
    exact hy
  refine ⟨res, Ψ, hθres, hres_surj, hres_T, ?_, hΨsurj, fun t => ?_⟩
  · exact hΨloc
  · rw [hΨπ t, hπ'def, RingHom.comp_apply]

end S_CuspForm_heckeLocal_exists_surjective_algHom_of_dvd
end P2MW
export P2MW.S_CuspForm_heckeLocal_exists_surjective_algHom_of_dvd (solution)
