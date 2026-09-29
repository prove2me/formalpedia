-- Prove2me | solution 1 for CuspidalType.exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0ed42680-1efa-5294-8bc1-66a4d65c0f3e

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Theorems.Thm_CuspidalType_exists_finset_monoidHom_mem_iff_forall_apply_eq_one_and_card_eq
import Theorems.Thm_CuspidalType_exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq
import Theorems.Thm_CuspidalType_charpoly_ind_torus_eq_prod_X_sub_C_of_forall_mem_iff
import Theorems.Thm_CuspidalType_finrank_eq_of_irreducible_of_cuspidal
import Theorems.Thm_CuspidalType_character_unipotent
import Theorems.Thm_CuspidalType_character_unipotent_mul_diagElem
import Theorems.Thm_CuspidalType_sum_character_eq_zero
import Theorems.Thm_CuspidalType_sum_character_mul_character_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central

set_option autoImplicit false

open CuspidalType

theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hirr : ∀ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ → W.toSubmodule = ⊤)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id) :
    ∃ θ : (GaloisField q 2)ˣ →* Kˣ, IsCuspidalOfType θ ρ := by
  classical

  have hK1 : Module.finrank K V = q - 1 := CuspidalType.finrank_eq_of_irreducible_of_cuspidal ρ hirr hcusp
  have hK2 : ∀ (c : (ZMod q)ˣ) (g : GL2 q), ρ.character (scalarElem q c * g) = ρ.character g := fun c g => by
    simp only [Representation.character, map_mul, hcent]
    rfl
  have hK3 : ∀ t : ZMod q, t ≠ 0 → ρ.character (unipotent q t) = -1 := fun t ht =>
    CuspidalType.character_unipotent ρ hirr hcusp ht
  have hK4 : ∀ (a : (ZMod q)ˣ) (s : ZMod q), a ≠ 1 → ρ.character (unipotent q s * diagElem q a) = 0 :=
    fun a s ha => CuspidalType.character_unipotent_mul_diagElem ρ hcusp ha s
  have hK5 : ∑ g : GL2 q, ρ.character g = 0 := CuspidalType.sum_character_eq_zero ρ hcusp
  have hK6 : ∑ g : GL2 q, ρ.character g * ρ.character g⁻¹ = Nat.card (GL2 q) :=
    CuspidalType.sum_character_mul_character_inv ρ hirr

  obtain ⟨S₀, hS₀, -⟩ := CuspidalType.exists_finset_monoidHom_mem_iff_forall_apply_eq_one_and_card_eq q K
  obtain ⟨θ, -, -, hθ⟩ :=
    CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq
      ρ hcent hK1 hK2 hK3 hK4 hK5 hK6 S₀ hS₀
  exact ⟨θ, ⟨hK1, hcusp, hcent, fun α => by
    rw [hθ α, CuspidalType.charpoly_ind_torus_eq_prod_X_sub_C_of_forall_mem_iff q K S₀ hS₀ α]⟩⟩

end S_CuspidalType_exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central
end P2MW
export P2MW.S_CuspidalType_exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central (solution)
