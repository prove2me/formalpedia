-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:34.129897+00:00
-- url     : https://prove2.me/submissions/3d7adc6b-40f9-4f8b-b4ba-5cd8d8b8c802

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_quot_ge
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_smul_top_pi
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_smul_top_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module
variable {O : Type} [CommRing O] [IsDedekindDomain O]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (p : Ideal O) [hp : p.IsMaximal] [Finite (O ⧸ p)] (Y : Type) [AddCommGroup Y]
    [Module O Y] [Module.Finite O Y] [Module.Projective O Y] :
    Nat.card (Y ⧸ p • (⊤ : Submodule O Y)) = Nat.card (O ⧸ p) ^ finrank O Y := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O Y
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfh : ∀ x, f (h x) = x := fun x => by
    have := congrArg (fun g => g x) hh; simpa using this
  set Q := LinearMap.ker f with hQ
  have : IsNoetherian O (Fin n → O) := isNoetherian_of_isNoetherianRing_of_finite _ _
  let φ : (Fin n → O) →ₗ[O] Y × Q :=
    f.prod ((LinearMap.id - h ∘ₗ f).codRestrict Q (fun x => by
      rw [hQ, LinearMap.mem_ker]; simp [hfh]))
  let ψ : Y × Q →ₗ[O] (Fin n → O) := h.coprod Q.subtype
  let e : (Fin n → O) ≃ₗ[O] Y × Q := LinearEquiv.ofLinearMap φ ψ
    (by
      ext x
      · simp [φ, ψ, hfh]
      · simp [φ, ψ, hfh]
      · have : f (x : Fin n → O) = 0 := x.2
        simp [φ, ψ, this]
      · have : f (x : Fin n → O) = 0 := x.2
        simp [φ, ψ, this])
    (by
      apply LinearMap.ext; intro x
      simp [φ, ψ])
  obtain ⟨fY, aY⟩ := s5b7_quot_ge p Y
  obtain ⟨fQ, aQ⟩ := s5b7_quot_ge p Q
  have hrank : finrank O Y + finrank O Q = n := by
    have := Submodule.finrank_quotient_add_finrank Q
    rw [(LinearMap.quotKerEquivOfSurjective f hf).finrank_eq] at this
    simpa using this
  have hF : (p • (⊤ : Submodule O (Fin n → O))).toAddSubgroup.index = Nat.card (O ⧸ p) ^ n := by
    have : (p • (⊤ : Submodule O (Fin n → O))).toAddSubgroup =
        AddSubgroup.pi Set.univ fun _ : Fin n => (Submodule.toAddSubgroup p) := by
      ext x
      simp only [Submodule.mem_toAddSubgroup, s5b7_smul_top_pi, AddSubgroup.mem_pi, Set.mem_univ,
        forall_true_left]
    rw [this, AddSubgroup.index_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
  have hPQ : (p • (⊤ : Submodule O (Y × Q))).toAddSubgroup.index =
      (p • (⊤ : Submodule O Y)).toAddSubgroup.index *
        (p • (⊤ : Submodule O Q)).toAddSubgroup.index := by
    rw [s5b7_smul_top_prod, ← AddSubgroup.index_prod]
    rfl
  have hE : (p • (⊤ : Submodule O (Fin n → O))).toAddSubgroup.index =
      (p • (⊤ : Submodule O (Y × Q))).toAddSubgroup.index := by
    have hm : (p • (⊤ : Submodule O (Fin n → O))).map (e : (Fin n → O) →ₗ[O] Y × Q) =
        p • (⊤ : Submodule O (Y × Q)) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
    exact Nat.card_congr (Submodule.Quotient.equiv _ _ e hm).toEquiv
  change (p • (⊤ : Submodule O Y)).toAddSubgroup.index = _
  change _ ≤ (p • (⊤ : Submodule O Y)).toAddSubgroup.index at aY
  change _ ≤ (p • (⊤ : Submodule O Q)).toAddSubgroup.index at aQ
  set a := (p • (⊤ : Submodule O Y)).toAddSubgroup.index with ha
  set b := (p • (⊤ : Submodule O Q)).toAddSubgroup.index with hb
  set k := Nat.card (O ⧸ p) with hk
  have hk0 : 0 < k := Nat.card_pos
  have hab : a * b = k ^ finrank O Y * k ^ finrank O Q := by
    rw [← hPQ, ← hE, hF, ← pow_add, hrank]
  by_contra hne
  have hlt : k ^ finrank O Y < a := lt_of_le_of_ne aY (Ne.symm hne)
  have hpos : 0 < k ^ finrank O Q := pow_pos hk0 _
  have : k ^ finrank O Y * k ^ finrank O Q < a * b :=
    calc k ^ finrank O Y * k ^ finrank O Q < a * k ^ finrank O Q :=
          Nat.mul_lt_mul_of_pos_right hlt hpos
      _ ≤ a * b := Nat.mul_le_mul_left _ aQ
  omega
end Formalism.HermitianLatticeCounting.P
