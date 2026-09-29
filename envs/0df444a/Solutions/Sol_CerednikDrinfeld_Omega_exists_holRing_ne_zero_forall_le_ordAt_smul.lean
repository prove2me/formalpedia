-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_holRing_ne_zero_forall_le_ordAt_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/93e56621-5256-5978-ae0e-581372faad76

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_CerednikDrinfeld_Omega_exists_isThetaPair_ordAt_eq_card
import Theorems.Thm_CerednikDrinfeld_Omega_ordAt_mul
import Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_upperHalfPlane_forall_pmoebius_ne_and_of_countable_of_archimedean
import Theorems.Thm_CerednikDrinfeld_Omega_countable_of_isDiscrete
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_isDomain_holRing
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_holRing_ne_zero_forall_le_ordAt_smul

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_holRing_ne_zero_forall_le_ordAt_smul.CerednikDrinfeld.Omega CerednikDrinfeld.Mumford"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.exists_isThetaPair_ordAt_eq_card Omega.ordAt_mul Omega.exists_mem_upperHalfPlane_forall_pmoebius_ne_and_of_countable_of_archimedean Omega.countable_of_isDiscrete Omega.finite_setOf_pmoebius_mem_affinoid Omega.isDomain_holRing Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid affinoid_mono IsExhausted holRing coe_smul_upperHalfPlane pmoebius upperHalfPlane coordSub_apply_self ordAt IsDiscrete exists_isThetaPair_ordAt_eq_card ordAt_mul exists_mem_upperHalfPlane_forall_pmoebius_ne_and_of_countable_of_archimedean countable_of_isDiscrete finite_setOf_pmoebius_mem_affinoid isDomain_holRing exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero"
namespace ThetaKillAux
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]

theorem ordAt_eq_zero_of_apply_ne_zero (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F : ↥(holRing ϖ)) (hF : F ≠ 0) (z : ↥(upperHalfPlane K₀ K))
    (hz : (F : ↥(upperHalfPlane K₀ K) → K) z ≠ 0) : ordAt ϖ F z = 0 := by
  obtain ⟨G, hG, -⟩ :=
    CerednikDrinfeld.Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero K₀ K hrk ϖ hex hfin F hF z
  by_contra h0
  apply hz
  have := congrArg (fun H : ↥(holRing ϖ) => (H : ↥(upperHalfPlane K₀ K) → K) z) hG
  simp only [Subring.coe_mul, Pi.mul_apply, SubmonoidClass.coe_pow, Pi.pow_apply, coordSub_apply_self] at this
  rw [this, zero_pow h0, zero_mul]

theorem ordAt_prod (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    [IsDomain ↥(holRing ϖ)]
    {ι : Type} (s : Finset ι) (f : ι → ↥(holRing ϖ)) (hf : ∀ i ∈ s, f i ≠ 0) (z : ↥(upperHalfPlane K₀ K)) :
    ordAt ϖ (∏ i ∈ s, f i) z = ∑ i ∈ s, ordAt ϖ (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact ordAt_eq_zero_of_apply_ne_zero ϖ hrk hex hfin 1 one_ne_zero z
      (by rw [OneMemClass.coe_one, Pi.one_apply]; exact one_ne_zero)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      CerednikDrinfeld.Omega.ordAt_mul K₀ K ϖ hrk hex hfin _ _ (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)) z,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem ordAt_pow (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    [IsDomain ↥(holRing ϖ)]
    (f : ↥(holRing ϖ)) (hf : f ≠ 0) (k : ℕ) (z : ↥(upperHalfPlane K₀ K)) :
    ordAt ϖ (f ^ k) z = k * ordAt ϖ f z := by
  have := ordAt_prod ϖ hrk hex hfin (Finset.range k) (fun _ => f) (fun _ _ => hf) z
  rw [Finset.prod_const, Finset.card_range, Finset.sum_const, Finset.card_range, smul_eq_mul] at this
  exact this

end CerednikDrinfeld.Omega.ThetaKillAux

open CerednikDrinfeld.Omega.ThetaKillAux in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {ι : Type} [Fintype ι] (b : ι → ↥(upperHalfPlane K₀ K)) (m : ι → ℕ) :
    ∃ H : ↥(holRing ϖ), H ≠ 0 ∧
      ∀ (i : ι) (γ : G), m i ≤ ordAt ϖ H (ρ γ • b i) := by
  classical
  haveI : Countable G := CerednikDrinfeld.Omega.countable_of_isDiscrete ϖ ρ hρ
  haveI : IsDomain ↥(holRing ϖ) := CerednikDrinfeld.Omega.isDomain_holRing K₀ K ϖ hrk hex hfin
  have hpair : ∀ i : ι, ∃ Hi : ↥(holRing ϖ), Hi ≠ 0 ∧ ∀ z : ↥(upperHalfPlane K₀ K),
      ordAt ϖ Hi z = Nat.card {γ : G // pmoebius K₀ (ρ γ) ((b i : ↥(upperHalfPlane K₀ K)) : K) = (z : K)} := by
    intro i
    obtain ⟨z₀, hz₀, hz₀a, hz₀b⟩ :=
      CerednikDrinfeld.Omega.exists_mem_upperHalfPlane_forall_pmoebius_ne_and_of_countable_of_archimedean
        K₀ K ϖ hrk ρ (b i).2 (b i).2
    obtain ⟨F, H, hFH, hord⟩ :=
      CerednikDrinfeld.Omega.exists_isThetaPair_ordAt_eq_card K₀ K ϖ hrk hex hfin ρ hρ (b i).2 (b i).2 hz₀ hz₀a hz₀b
    exact ⟨H, nonZeroDivisors.ne_zero hFH.1, fun z => (hord z).2⟩
  choose Hf hH0 hord using hpair
  refine ⟨∏ i, Hf i ^ m i, Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hH0 i), ?_⟩
  intro i γ
  set z : ↥(upperHalfPlane K₀ K) := ρ γ • b i with hz
  rw [ordAt_prod ϖ hrk hex hfin Finset.univ (fun j => Hf j ^ m j) (fun j _ => pow_ne_zero _ (hH0 j)) z]
  have hle : ordAt ϖ (Hf i ^ m i) z ≤ ∑ j ∈ Finset.univ, ordAt ϖ (Hf j ^ m j) z :=
    Finset.single_le_sum (f := fun j => ordAt ϖ (Hf j ^ m j) z) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  refine le_trans ?_ hle
  rw [ordAt_pow ϖ hrk hex hfin (Hf i) (hH0 i) (m i) z, hord i z]

  have hzval : ((z : ↥(upperHalfPlane K₀ K)) : K) = pmoebius K₀ (ρ γ) ((b i : ↥(upperHalfPlane K₀ K)) : K) := by
    rw [hz, coe_smul_upperHalfPlane]
  haveI : Nonempty {γ' : G // pmoebius K₀ (ρ γ') ((b i : ↥(upperHalfPlane K₀ K)) : K) = (z : K)} :=
    ⟨⟨γ, hzval.symm⟩⟩
  haveI : Finite {γ' : G // pmoebius K₀ (ρ γ') ((b i : ↥(upperHalfPlane K₀ K)) : K) = (z : K)} := by
    obtain ⟨n₁, hn₁⟩ := hex (z : K) z.2
    obtain ⟨n₂, hn₂⟩ := hex ((b i : ↥(upperHalfPlane K₀ K)) : K) (b i).2
    have hn : (z : K) ∈ affinoid ϖ (max n₁ n₂) := affinoid_mono ϖ (le_max_left _ _) hn₁
    have hb : ((b i : ↥(upperHalfPlane K₀ K)) : K) ∈ affinoid ϖ (max n₁ n₂) := affinoid_mono ϖ (le_max_right _ _) hn₂
    have hf := CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid ϖ ρ hρ (max n₁ n₂) hb
    refine Set.Finite.to_subtype (hf.subset ?_)
    intro γ' hγ'
    simp only [Set.mem_setOf_eq] at hγ' ⊢
    rw [hγ']; exact hn
  have hc : 1 ≤ Nat.card {γ' : G // pmoebius K₀ (ρ γ') ((b i : ↥(upperHalfPlane K₀ K)) : K) = (z : K)} :=
    Nat.card_pos
  calc m i = m i * 1 := (mul_one _).symm
    _ ≤ m i * Nat.card {γ' : G // pmoebius K₀ (ρ γ') ((b i : ↥(upperHalfPlane K₀ K)) : K) = (z : K)} :=
        Nat.mul_le_mul_left _ hc

end S_CerednikDrinfeld_Omega_exists_holRing_ne_zero_forall_le_ordAt_smul
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_holRing_ne_zero_forall_le_ordAt_smul (solution)
