-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.projective_quotient_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:53.0365+00:00
-- url     : https://prove2.me/submissions/585d2074-cc26-473d-84be-d11579e6fc3c

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_index_ideal_smul_le_norm_pow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_mem_ideal_smul_top_pi_iff
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ideal_smul_top_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.SLP.P.CountO NumberField
open scoped nonZeroDivisors
open NumberField Formalism.SLP.P.CountO
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ProjQuotCard := by
  intro E _ _ P _ _ _ _ I hI
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) P
  obtain ⟨h, hfh⟩ := Module.projective_lifting_property f (LinearMap.id) hf
  have hfh' : ∀ x, f (h x) = x := fun x => LinearMap.congr_fun hfh x
  set Q := LinearMap.ker f with hQ
  let φ : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E) := h.coprod Q.subtype
  have hφinj : Function.Injective φ := by
    rintro ⟨x, q⟩ ⟨x', q'⟩ hxy
    simp only [φ, LinearMap.coprod_apply, Submodule.coe_subtype] at hxy
    have h1 := congrArg f hxy
    rw [map_add, map_add, hfh', hfh', LinearMap.mem_ker.1 q.2, LinearMap.mem_ker.1 q'.2,
      add_zero, add_zero] at h1
    subst h1
    exact Prod.ext rfl (Subtype.ext (add_left_cancel hxy))
  have hφsurj : Function.Surjective φ := by
    intro y
    refine ⟨(f y, ⟨y - h (f y), ?_⟩), ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hfh', sub_self]
    · simp [φ]
  let e := LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hhinj : Function.Injective h := fun x y hxy => by
    rw [← hfh' x, ← hfh' y, hxy]

  have hpi : (I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).toAddSubgroup =
      AddSubgroup.pi Set.univ (fun _ => (I : Submodule (𝓞 E) (𝓞 E)).toAddSubgroup) := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
    exact mem_ideal_smul_top_pi_iff I n x
  have hfree : (I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).toAddSubgroup.index =
      Ideal.absNorm I ^ n := by
    rw [hpi, AddSubgroup.index_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
  have hcomap : (I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).comap
      (e : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E)) = I • ⊤ := by
    rw [Submodule.comap_equiv_eq_map_symm, Submodule.map_smul'', Submodule.map_top,
      LinearEquiv.range]
  have hprod_idx : (I • (⊤ : Submodule (𝓞 E) (P × Q))).toAddSubgroup.index =
      Ideal.absNorm I ^ n := by
    have hc : ((I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).comap
        (e : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E))).toAddSubgroup =
        (I • (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E))).toAddSubgroup.comap
          (e : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E)).toAddMonoidHom := by
      ext x; rfl
    rw [← hcomap, ← hfree, hc]
    exact AddSubgroup.index_comap_of_surjective _ e.surjective
  rw [ideal_smul_top_prod] at hprod_idx
  rw [show ((I • (⊤ : Submodule (𝓞 E) P)).prod (I • (⊤ : Submodule (𝓞 E) Q))).toAddSubgroup =
      (I • (⊤ : Submodule (𝓞 E) P)).toAddSubgroup.prod
        (I • (⊤ : Submodule (𝓞 E) Q)).toAddSubgroup from rfl, AddSubgroup.index_prod] at hprod_idx

  set r := finrank (𝓞 E) P
  have hTFP : TF E P := by
    intro a ha x hx
    have : a • h x = 0 := by rw [← map_smul, hx, map_zero]
    rw [smul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 ha
    · rw [← hfh' x, h0, map_zero]
  have hTFQ : TF E Q := by
    intro a ha x hx
    have : a • (x : Fin n → 𝓞 E) = 0 := by rw [← Submodule.coe_smul, hx, Submodule.coe_zero]
    rw [smul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 ha
    · exact Subtype.ext h0
  have hLIBP : LIB E P r := fun ι _ v hv => hv.fintype_card_le_finrank
  obtain ⟨a, ha⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := P) (le_refl r)
  have hrn : r ≤ n := by
    have := (ha.map' h (LinearMap.ker_eq_bot.2 hhinj)).fintype_card_le_finrank
    simpa [Module.finrank_fin_fun] using this
  have hLIBQ : LIB E Q (n - r) := by
    intro ι _ v hv
    have hc := linearIndependent_inl_union_inr' ha hv
    have hc' := (hc.map' (e : (P × Q) →ₗ[𝓞 E] (Fin n → 𝓞 E))
      (LinearMap.ker_eq_bot.2 e.injective)).fintype_card_le_finrank
    rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at hc'
    omega
  obtain ⟨hP1, hP2⟩ := index_ideal_smul_le_norm_pow (E := E) r _ I hI rfl P hTFP hLIBP
  obtain ⟨hQ1, hQ2⟩ := index_ideal_smul_le_norm_pow (E := E) (n - r) _ I hI rfl Q hTFQ hLIBQ
  have hN : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  change (I • (⊤ : Submodule (𝓞 E) P)).toAddSubgroup.index = _
  by_contra hne
  have hlt := lt_of_le_of_ne hP2 hne
  have hpos : 0 < Ideal.absNorm I ^ (n - r) := pow_pos hN _
  have : (I • (⊤ : Submodule (𝓞 E) P)).toAddSubgroup.index *
      (I • (⊤ : Submodule (𝓞 E) Q)).toAddSubgroup.index <
      Ideal.absNorm I ^ r * Ideal.absNorm I ^ (n - r) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ hQ2) (Nat.mul_lt_mul_of_pos_right hlt hpos)
  rw [← pow_add, Nat.add_sub_cancel' hrn, hprod_idx] at this
  exact lt_irrefl _ this
end Formalism.HermitianLatticeCounting.P
