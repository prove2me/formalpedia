-- Prove2me | solution 1 for CerednikDrinfeld.relIndex_finiteIdeleStabilizer_meetOrder_eq_succ_of_mem_primeHeckeSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/27e51fbb-afb3-5277-ab67-205f9864e265

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_Subgroup_relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq
import Theorems.Thm_CerednikDrinfeld_natCard_setOf_exists_mem_primeHeckeSet_quotientMk_eq_eq_succ_of_prime
import Theorems.Thm_QuaternionAlgebra_primeHeckeSet_eq_doubleCoset_finiteIdeleStabilizer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_relIndex_finiteIdeleStabilizer_meetOrder_eq_succ_of_mem_primeHeckeSet
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct Quaternion NumberField Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace CSTowerT21
namespace Stab

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" w => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w

noncomputable abbrev evU (w : HeightOneSpectrum (𝓞 ℚ)) :
    (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ →* (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ :=
  Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom

def boxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Set (ℍ𝔸) :=
  {x | ∃ z ∈ Λ, ∃ c : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_box_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ𝔸} :
    x ∈ Submodule.finiteAdeleBox Λ ↔ x ∈ Submodule.span ℤ (boxGen Λ) := by
  have e : Submodule.finiteAdeleBox Λ = (Submodule.span ℤ (boxGen Λ)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [e]; rfl

theorem box_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {x y : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  rw [mem_box_iff_span] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, fun v => ?_, ?_⟩
      · have e : (c' * c) v = c' v * c v := rfl
        rw [e]
        exact mul_mem (hc' v) (hc v)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) : (1 : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, fun v => ?_, rfl⟩
  have e : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl
  rw [e]; exact one_mem _

theorem mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  constructor
  · intro hu
    have key : ∀ w : (ℍ𝔸)ˣ, w ∈ Submodule.finiteIdeleStabilizer Λ → (w : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
      intro w hw
      have h := (Submodule.mem_finiteIdeleStabilizer_iff Λ w).mp hw
      have h1 : (w : ℍ𝔸) * 1 ∈ w • ((Submodule.finiteAdeleBox Λ : AddSubgroup ℍ𝔸) : Set ℍ𝔸) :=
        Set.smul_mem_smul_set (one_mem_box hΛ)
      rw [h, mul_one] at h1
      exact h1
    exact ⟨key u hu, key u⁻¹ (inv_mem hu)⟩
  · rintro ⟨hu, hui⟩
    rw [Submodule.mem_finiteIdeleStabilizer_iff]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact box_mul_mem hΛ hu hx
    · intro x hx
      refine ⟨(u⁻¹ : (ℍ𝔸)ˣ) • x, box_mul_mem hΛ hui hx, ?_⟩
      show (u : ℍ𝔸) * (((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x) = x
      rw [← mul_assoc, Units.mul_inv, one_mul]

theorem isOrder_meetOrder {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (g : (ℍ𝔸)ˣ) :
    IsOrder (meetOrder R g) :=
  hR.inf (IsOrder.conjByFiniteIdele R hR g)

theorem mem_finiteIdeleStabilizer_meetOrder_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (g u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer (meetOrder R g) ↔
      u ∈ Submodule.finiteIdeleStabilizer R ∧ g⁻¹ * u * g ∈ Submodule.finiteIdeleStabilizer R := by
  obtain ⟨hbox, -, hle, hconj⟩ := IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le R hR g
  constructor
  · intro hu
    exact ⟨hle hu, hconj u hu⟩
  · rintro ⟨hu, hgu⟩
    have hRg : IsOrder (meetOrder R g) := isOrder_meetOrder hR g
    rw [mem_stabilizer_iff hR] at hu hgu
    rw [mem_stabilizer_iff hRg]
    rw [show meetOrder R g = R ⊓ Submodule.conjByFiniteIdele R g from rfl, hbox]
    have key : ∀ w : ℍ𝔸, w ∈ Submodule.finiteAdeleBox R →
        ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * w * (g : ℍ𝔸) ∈ Submodule.finiteAdeleBox R →
        w ∈ Submodule.finiteAdeleBox R ⊓ (Submodule.finiteAdeleBox R).map
          ((AddMonoidHom.mulRight ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)).comp (AddMonoidHom.mulLeft (g : ℍ𝔸))) := by
      intro w hw hgw
      refine ⟨hw, ⟨_, hgw, ?_⟩⟩
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
      rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
    refine ⟨key _ hu.1 ?_, key _ hu.2 ?_⟩
    · simpa only [Units.val_mul] using hgu.1
    · have e : (((g⁻¹ * u * g)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (g : ℍ𝔸) := by
        rw [mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, mul_assoc]
      rw [← e]; exact hgu.2

theorem finiteIdeleStabilizer_meetOrder_eq {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (g : (ℍ𝔸)ˣ) :
    Submodule.finiteIdeleStabilizer (meetOrder R g) =
      Submodule.finiteIdeleStabilizer R ⊓ (Submodule.finiteIdeleStabilizer R).map (MulAut.conj g).toMonoidHom := by
  ext u
  rw [mem_finiteIdeleStabilizer_meetOrder_iff hR, Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

def localBoxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_localBox_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)}
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} :
    x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.span ℤ (localBoxGen Λ v) := by
  have : Submodule.localBox Λ v = (Submodule.span ℤ (localBoxGen Λ v)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl

theorem finiteAdeleEvalAt_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {x : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) :
    (ev v) x ∈ Submodule.localBox Λ v := by
  rw [mem_box_iff_span] at hx
  rw [mem_localBox_iff_span]
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c v, hc v, ?_⟩
    simp [Submodule.finiteAdeleEvalAt, Submodule.finiteAdeleEvalAlgHom_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [map_zsmul]; exact Submodule.smul_mem _ _ h₁

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, mul_mem hc' hc, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span]
  exact Submodule.subset_span ⟨1, hΛ.one_mem, 1, one_mem _, rfl⟩

theorem ev_smul (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ𝔸) : (ev v) (c • x) = c • (ev v) x := map_smul _ _ _

theorem ratSmul_eq_one_tmul_mul (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    c • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) c) * x := by
  have e1 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) c) = c • (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := by
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rw [e1, smul_mul_assoc, one_mul]

theorem smul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ)) {c : ℚ}
    (hc : algebraMap ℚ (v.adicCompletion ℚ) c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) : c • x ∈ Submodule.localBox Λ v := by
  rw [ratSmul_eq_one_tmul_mul, mem_localBox_iff_span]
  rw [mem_localBox_iff_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    refine Submodule.subset_span ⟨z, hz, algebraMap ℚ (v.adicCompletion ℚ) c * c', mul_mem hc hc', ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem inv_natCast_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hnv : ((n : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ((n : v.adicCompletion ℚ))⁻¹ ∈ v.adicCompletionIntegers ℚ := by
  have h1 : ((n : ℕ) : v.adicCompletion ℚ) = algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) ((n : ℕ) : 𝓞 ℚ) := by
    rw [map_natCast]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v ((n : ℕ) : 𝓞 ℚ)
  erw [h2, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) v).mpr hnv, inv_one]

theorem algebraMap_inv_natCast_mem (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hnv : ((n : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    algebraMap ℚ (v.adicCompletion ℚ) ((n : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ := by
  rw [map_inv₀, map_natCast]; exact inv_natCast_mem_adicCompletionIntegers v n hnv

theorem ev_mem_localBox_of_smul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} {c : ℕ} (hc : c ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((c : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) {y : ℍ𝔸} (hy : (c : ℚ) • y ∈ Submodule.finiteAdeleBox Λ) :
    (ev v) y ∈ Submodule.localBox Λ v := by
  have := smul_mem_localBox v (algebraMap_inv_natCast_mem v c hv) (finiteAdeleEvalAt_mem_localBox v hy)
  rwa [ev_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc : (c : ℚ) ≠ 0), one_smul] at this

theorem natGenerator_dvd_iff' (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Rat.HeightOneSpectrum.natGenerator v ∣ n ↔ ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n,
    Ideal.apply_mem_of_equiv_iff]

theorem not_mem_of_prime_ne {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hne : ℓ ≠ p) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
  intro hℓv
  rw [← natGenerator_dvd_iff'] at hv hℓv
  have h1 := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp).mp hv
  have h2 := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hℓv
  exact hne (h2.symm.trans h1)

theorem exists_place (p : ℕ) (hp : p.Prime) : ∃ v : HeightOneSpectrum (𝓞 ℚ), ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  refine ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩, ?_⟩
  rw [← natGenerator_dvd_iff']
  have : Rat.HeightOneSpectrum.natGenerator ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩) = p := by
    have e := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, hp⟩
    exact congrArg Subtype.val e
  rw [this]

theorem mem_localBoxUnits_iff' (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ))
    (t : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    t ∈ Submodule.localBoxUnits Λ v ↔
      (t : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v ∧
        ((t⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v :=
  Submodule.mem_localBoxUnits_iff Λ v t

theorem conj_mem_localBoxUnits_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ} (hg : g ∈ Submodule.localBoxUnits Λ v)
    (t : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    g⁻¹ * t * g ∈ Submodule.localBoxUnits Λ v ↔ t ∈ Submodule.localBoxUnits Λ v := by
  rw [mem_localBoxUnits_iff'] at hg
  have key : ∀ s : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ, s ∈ Submodule.localBoxUnits Λ v →
      g⁻¹ * s * g ∈ Submodule.localBoxUnits Λ v := by
    intro s hs
    rw [mem_localBoxUnits_iff'] at hs ⊢
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul]
      exact localBox_mul_mem hΛ v (localBox_mul_mem hΛ v hg.2 hs.1) hg.1
    · rw [mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
      exact localBox_mul_mem hΛ v hg.2 (localBox_mul_mem hΛ v hs.2 hg.1)
  constructor
  · intro h
    have hgi : g⁻¹ ∈ Submodule.localBoxUnits Λ v := by
      rw [mem_localBoxUnits_iff', inv_inv]; exact ⟨hg.2, hg.1⟩
    have h2 := key _ h

    have key' : ∀ s : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ, s ∈ Submodule.localBoxUnits Λ v →
        g * s * g⁻¹ ∈ Submodule.localBoxUnits Λ v := by
      intro s hs
      rw [mem_localBoxUnits_iff'] at hs ⊢
      refine ⟨?_, ?_⟩
      · rw [Units.val_mul, Units.val_mul]
        exact localBox_mul_mem hΛ v (localBox_mul_mem hΛ v hg.1 hs.1) hg.2
      · rw [mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
        exact localBox_mul_mem hΛ v hg.1 (localBox_mul_mem hΛ v hs.2 hg.2)
    have h3 := key' _ h
    have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
    rwa [e] at h3
  · exact key t

theorem map_mem_localBoxUnits_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {u : (ℍ𝔸)ˣ}
    (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits Λ v :=
  (IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ hΛ u).mp hu v

theorem map_mem_localBoxUnits_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]} {p : ℕ} (hp : p ≠ 0)
    {g : (ℍ𝔸)ˣ} (hg : g ∈ primeHeckeSet Λ p) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ((p : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    (evU (a := a) (b := b) v) g ∈ Submodule.localBoxUnits Λ v := by
  obtain ⟨h1, h2, -, -⟩ := hg
  rw [mem_localBoxUnits_iff', Units.coe_map, Units.coe_map_inv]
  exact ⟨finiteAdeleEvalAt_mem_localBox v h1, ev_mem_localBox_of_smul_mem hp v hv h2⟩

theorem mem_localBoxUnits_meetOrder_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (g : (ℍ𝔸)ˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (t : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    t ∈ Submodule.localBoxUnits (meetOrder R g) v ↔
      t ∈ Submodule.localBoxUnits R v ∧ ((evU (a := a) (b := b) v) g)⁻¹ * t * (evU (a := a) (b := b) v) g ∈ Submodule.localBoxUnits R v := by
  have hc : IsOrder (Submodule.conjByFiniteIdele R g) := IsOrder.conjByFiniteIdele R hR g
  have hbox : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ∈ Submodule.localBox (meetOrder R g) v ↔
      x ∈ Submodule.localBox R v ∧
        (ev v) ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * (ev v) (g : ℍ𝔸) ∈ Submodule.localBox R v := by
    intro x
    rw [show meetOrder R g = R ⊓ Submodule.conjByFiniteIdele R g from rfl,
      Submodule.localBox_inf R (Submodule.conjByFiniteIdele R g) hR.fg hR.spanTop hc.fg hc.spanTop v,
      AddSubgroup.mem_inf, Submodule.mem_localBox_conjByFiniteIdele_iff R hR.fg hR.spanTop g v]
    have i3 : (ev v) (g : ℍ𝔸) * (ev v) ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have i4 : (ev v) ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (ev v) (g : ℍ𝔸) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    refine and_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      rw [← mul_assoc, ← mul_assoc, i4, one_mul, mul_assoc, i4, mul_one]; exact hy
    · intro h
      refine ⟨_, h, ?_⟩
      rw [← mul_assoc, ← mul_assoc, i3, one_mul, mul_assoc, i3, mul_one]
  rw [mem_localBoxUnits_iff', mem_localBoxUnits_iff', mem_localBoxUnits_iff', hbox, hbox]
  simp only [Units.val_mul, Units.coe_map, Units.coe_map_inv, mul_inv_rev, inv_inv, MonoidHom.coe_coe,
    RingHom.coe_coe, RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, h3⟩, by simpa only [mul_assoc, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_toRingHom] using h2,
      by simpa only [mul_assoc, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_toRingHom] using h4⟩
  · rintro ⟨⟨h1, h3⟩, h2, h4⟩
    exact ⟨⟨h1, by simpa only [mul_assoc, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_toRingHom] using h2⟩, h3,
      by simpa only [mul_assoc, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_toRingHom] using h4⟩

theorem one_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) ∈ Submodule.localBoxUnits Λ v := by
  rw [mem_localBoxUnits_iff', inv_one, Units.val_one]
  exact ⟨one_mem_localBox hΛ v, one_mem_localBox hΛ v⟩

theorem mem_stabilizer_iff_forall {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔ ∀ v, (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits Λ v :=
  IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ hΛ u

theorem eq_of_natCast_prime_mem {ℓ : ℕ} (hℓ : ℓ.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((ℓ : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  apply Subtype.ext
  show Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator w
  rw [← natGenerator_dvd_iff'] at hv hw
  rw [(Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hv,
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hℓ).mp hw]

theorem mem_stabilizer_tower_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime)
    (hℓq : ℓ ≠ q) {n m n' : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q) (hm : m ∈ primeHeckeSet R ℓ)
    (hn' : n' ∈ primeHeckeSet (meetOrder R m) q) (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R m) n') ↔
      u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) ∧ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R m) := by
  have hR' : IsOrder (meetOrder R m) := isOrder_meetOrder hR m
  have hS : IsOrder (meetOrder R n) := isOrder_meetOrder hR n
  have hS' : IsOrder (meetOrder (meetOrder R m) n') := isOrder_meetOrder hR' n'
  rw [mem_stabilizer_iff_forall hS', mem_stabilizer_iff_forall hS, mem_stabilizer_iff_forall hR', ← forall_and]
  refine forall_congr' fun v => ?_
  rw [mem_localBoxUnits_meetOrder_iff hR' n' v, mem_localBoxUnits_meetOrder_iff hR n v]
  by_cases hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
  ·
    have hℓv := not_mem_of_prime_ne hq hℓ hℓq hqv
    have hmv := map_mem_localBoxUnits_of_mem_primeHeckeSet hℓ.ne_zero hm hℓv
    have hw := map_mem_localBoxUnits_of_mem_stabilizer hR hnn' v
    have hR'U : ∀ s, s ∈ Submodule.localBoxUnits (meetOrder R m) v ↔ s ∈ Submodule.localBoxUnits R v := fun s => by
      rw [mem_localBoxUnits_meetOrder_iff hR m v, conj_mem_localBoxUnits_iff hR v hmv, and_self]
    have e : (evU (a := a) (b := b) v) n' = (evU (a := a) (b := b) v) n * (evU (a := a) (b := b) v) (n⁻¹ * n') := by
      rw [← map_mul, mul_inv_cancel_left]
    have e2 : ((evU (a := a) (b := b) v) n')⁻¹ * (evU (a := a) (b := b) v) u * (evU (a := a) (b := b) v) n' =
        ((evU (a := a) (b := b) v) (n⁻¹ * n'))⁻¹ *
          (((evU (a := a) (b := b) v) n)⁻¹ * (evU (a := a) (b := b) v) u * (evU (a := a) (b := b) v) n) *
          (evU (a := a) (b := b) v) (n⁻¹ * n') := by
      rw [e]; group
    rw [hR'U, hR'U, e2, conj_mem_localBoxUnits_iff hR v hw]
    tauto
  ·
    have hnv := map_mem_localBoxUnits_of_mem_primeHeckeSet hq.ne_zero hn hqv
    have hn'v := map_mem_localBoxUnits_of_mem_primeHeckeSet hq.ne_zero hn' hqv
    have hsub : (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits (meetOrder R m) v →
        (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits R v := fun h =>
      ((mem_localBoxUnits_meetOrder_iff hR m v _).mp h).1
    rw [conj_mem_localBoxUnits_iff hR' v hn'v, conj_mem_localBoxUnits_iff hR v hnv]
    tauto

theorem exists_mem_stabilizer_meetOrder_inv_mul_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ}
    (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) {n m : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q)
    (hm : m ∈ primeHeckeSet R ℓ) (u : (ℍ𝔸)ˣ) (hu : u ∈ Submodule.finiteIdeleStabilizer R) :
    ∃ k ∈ Submodule.finiteIdeleStabilizer (meetOrder R m), k⁻¹ * u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := by
  classical
  have hR' : IsOrder (meetOrder R m) := isOrder_meetOrder hR m
  have hS : IsOrder (meetOrder R n) := isOrder_meetOrder hR n
  obtain ⟨vℓ, hvℓ⟩ := exists_place ℓ hℓ
  obtain ⟨β, hβ1, hβ2⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) {vℓ}
    (fun v => ((evU (a := a) (b := b) v) u)⁻¹)
  have eβ : ∀ v, (evU (a := a) (b := b) v) β = if v = vℓ then ((evU (a := a) (b := b) v) u)⁻¹ else 1 := by
    intro v
    apply Units.ext
    by_cases hv : v = vℓ
    · rw [if_pos hv]; exact hβ1 v (by rw [Finset.mem_singleton]; exact hv)
    · rw [if_neg hv]; exact hβ2 v (by rw [Finset.mem_singleton]; exact hv)
  have huv : ∀ v, (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits R v :=
    fun v => map_mem_localBoxUnits_of_mem_stabilizer hR hu v
  refine ⟨u * β, ?_, ?_⟩
  · rw [mem_stabilizer_iff_forall hR']
    intro v
    rw [mem_localBoxUnits_meetOrder_iff hR m v, map_mul, eβ v]
    by_cases hv : v = vℓ
    · rw [if_pos hv, mul_inv_cancel, mul_one, inv_mul_cancel]
      exact ⟨one_mem_localBoxUnits hR v, one_mem_localBoxUnits hR v⟩
    · rw [if_neg hv, mul_one]
      have hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (eq_of_natCast_prime_mem hℓ h hvℓ)
      have hmv := map_mem_localBoxUnits_of_mem_primeHeckeSet hℓ.ne_zero hm hℓv
      exact ⟨huv v, (conj_mem_localBoxUnits_iff hR v hmv _).mpr (huv v)⟩
  · have e : (u * β)⁻¹ * u = β⁻¹ := by group
    rw [e, mem_stabilizer_iff_forall hS]
    intro v
    rw [mem_localBoxUnits_meetOrder_iff hR n v, map_inv, eβ v]
    by_cases hv : v = vℓ
    · subst hv
      rw [if_pos rfl, inv_inv]
      have hqv : ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := not_mem_of_prime_ne hℓ hq (Ne.symm hℓq) hvℓ
      have hnv := map_mem_localBoxUnits_of_mem_primeHeckeSet hq.ne_zero hn hqv
      exact ⟨huv v, (conj_mem_localBoxUnits_iff hR v hnv _).mpr (huv v)⟩
    · rw [if_neg hv, inv_one, mul_one, inv_mul_cancel]
      exact ⟨one_mem_localBoxUnits hR v, one_mem_localBoxUnits hR v⟩

theorem exists_mem_stabilizer_meetOrder_inv_mul_mem' {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ}
    (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) {n m : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q)
    (hm : m ∈ primeHeckeSet R ℓ) (u : (ℍ𝔸)ˣ) (hu : u ∈ Submodule.finiteIdeleStabilizer R) :
    ∃ k ∈ Submodule.finiteIdeleStabilizer (meetOrder R n), k⁻¹ * u ∈ Submodule.finiteIdeleStabilizer (meetOrder R m) := by
  obtain ⟨k, hk, hku⟩ := exists_mem_stabilizer_meetOrder_inv_mul_mem hR hq hℓ hℓq hn hm u⁻¹ (inv_mem hu)
  refine ⟨u * k, ?_, ?_⟩
  · have e : u * k = (k⁻¹ * u⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem hku
  · have e : (u * k)⁻¹ * u = k⁻¹ := by group
    rw [e]; exact inv_mem hk

end CSTowerT21.Stab

namespace CSTowerT21
namespace HL

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

def boxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ𝔸 :=
  {x | ∃ z ∈ Λ, ∃ c : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] c}

theorem box_eq_span (Λ : Submodule ℤ ℍ[ℚ, a, b]) :
    Submodule.finiteAdeleBox Λ = (Submodule.span ℤ (boxGen Λ)).toAddSubgroup := by
  rw [Submodule.span_int_eq_addSubgroupClosure]; rfl

theorem mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ𝔸} :
    x ∈ Submodule.finiteAdeleBox Λ ↔ x ∈ Submodule.span ℤ (boxGen Λ) := by
  rw [box_eq_span]; rfl

theorem box_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x y : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  rw [mem_box_iff] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, fun v => ?_, ?_⟩
      · have e : (c' * c) v = c' v * c v := rfl
        rw [e]
        exact mul_mem (hc' v) (hc v)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) :
    (1 : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, fun v => ?_, ?_⟩
  · have e : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl
    rw [e]; exact one_mem _
  · rfl

theorem coe_mem_box_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  have h := (Submodule.mem_finiteIdeleStabilizer_iff Λ u).mp hu

  have h1 : (u : ℍ𝔸) * 1 ∈ u • ((Submodule.finiteAdeleBox Λ : AddSubgroup ℍ𝔸) : Set ℍ𝔸) :=
    Set.smul_mem_smul_set (one_mem_box hΛ)
  rw [h, mul_one] at h1
  exact h1

theorem coe_inv_mem_box_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  coe_mem_box_of_mem_stabilizer hΛ (inv_mem hu)

theorem mul_mem_primeHeckeSet_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (ℓ : ℕ) {u h : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ) :
    u * h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hub := coe_mem_box_of_mem_stabilizer hΛ hu
  have huib := coe_inv_mem_box_of_mem_stabilizer hΛ hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact box_mul_mem hΛ hub h1
  · rw [mul_inv_rev, Units.val_mul, ← smul_mul_assoc]
    exact box_mul_mem hΛ h2 huib
  · intro hmem
    apply h3
    have : ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (((u * h)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (u : ℍ𝔸) := by
      rw [mul_inv_rev, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact box_mul_mem hΛ hmem hub
  · intro hmem
    apply h4
    have : (ℓ : ℚ)⁻¹ • (h : ℍ𝔸) = ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((ℓ : ℚ)⁻¹ • ((u * h : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
      rw [mul_smul_comm, Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]; exact box_mul_mem hΛ huib hmem

theorem mul_mem_primeHeckeSet_of_mem_stabilizer' {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (ℓ : ℕ) {u h : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ) :
    h * u ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hub := coe_mem_box_of_mem_stabilizer hΛ hu
  have huib := coe_inv_mem_box_of_mem_stabilizer hΛ hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact box_mul_mem hΛ h1 hub
  · rw [mul_inv_rev, Units.val_mul, ← mul_smul_comm]
    exact box_mul_mem hΛ huib h2
  · intro hmem
    apply h3
    have : ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (u : ℍ𝔸) * (((h * u)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
      rw [mul_inv_rev, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
    rw [this]; exact box_mul_mem hΛ hub hmem
  · intro hmem
    apply h4
    have : (ℓ : ℚ)⁻¹ • (h : ℍ𝔸) = ((ℓ : ℚ)⁻¹ • ((h * u : (ℍ𝔸)ˣ) : ℍ𝔸)) * ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
      rw [smul_mul_assoc, Units.val_mul, mul_assoc, Units.mul_inv, mul_one]
    rw [this]; exact box_mul_mem hΛ hmem huib

theorem box_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') :
    Submodule.finiteAdeleBox Λ ≤ Submodule.finiteAdeleBox Λ' := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem mem_stabilizer_of_coe_mem_of_coe_inv_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ) (hui : ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ := by
  rw [Submodule.mem_finiteIdeleStabilizer_iff]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact box_mul_mem hΛ hu hx
  · intro x hx
    refine ⟨(u⁻¹ : (ℍ𝔸)ˣ) • x, box_mul_mem hΛ hui hx, ?_⟩
    show (u : ℍ𝔸) * (((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x) = x
    rw [← mul_assoc, Units.mul_inv, one_mul]

theorem stabilizer_mono {S R : Submodule ℤ ℍ[ℚ, a, b]} (hS : QuaternionAlgebra.IsOrder S) (hR : QuaternionAlgebra.IsOrder R)
    (h : S ≤ R) : Submodule.finiteIdeleStabilizer S ≤ Submodule.finiteIdeleStabilizer R := by
  intro u hu
  exact mem_stabilizer_of_coe_mem_of_coe_inv_mem hR (box_mono h (coe_mem_box_of_mem_stabilizer hS hu))
    (box_mono h (coe_inv_mem_box_of_mem_stabilizer hS hu))

theorem mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  ⟨fun hu => ⟨coe_mem_box_of_mem_stabilizer hΛ hu, coe_inv_mem_box_of_mem_stabilizer hΛ hu⟩,
   fun h => mem_stabilizer_of_coe_mem_of_coe_inv_mem hΛ h.1 h.2⟩

def localBoxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_localBox_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)} {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} :
    x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.span ℤ (localBoxGen Λ v) := by
  have : Submodule.localBox Λ v = (Submodule.span ℤ (localBoxGen Λ v)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl

theorem finiteAdeleEvalAt_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {x : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v x ∈ Submodule.localBox Λ v := by
  rw [mem_box_iff] at hx
  rw [mem_localBox_iff_span]
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c v, hc v, ?_⟩
    simp [Submodule.finiteAdeleEvalAt, Submodule.finiteAdeleEvalAlgHom_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [map_zsmul]; exact Submodule.smul_mem _ _ h₁

theorem tmul_one_mul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c * c', mul_mem hc hc', ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (ℓ : ℕ) {h : (ℍ𝔸)ˣ} (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hℓv : algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ) :
    Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h ∈ Submodule.localBoxUnits Λ v := by
  obtain ⟨h1, h2, -, h4⟩ := hh
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓpos
  · exfalso; apply h4
    rw [Nat.cast_zero, inv_zero, zero_smul]; exact zero_mem _
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓpos.ne'
  rw [Submodule.mem_localBoxUnits_iff]
  refine ⟨finiteAdeleEvalAt_mem_localBox v h1, ?_⟩

  set f := Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v with hf
  have e1 : (((Units.map f.toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
      = f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := Units.coe_map_inv _ _
  have e2 : f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) * f ((ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
    rw [map_smul, ← Algebra.TensorProduct.algebraMap_apply', ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hℓ0, one_smul]
  show (((Units.map f.toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ _
  rw [e1, e2]
  exact tmul_one_mul_mem_localBox v hℓv (finiteAdeleEvalAt_mem_localBox v h2)

theorem localBox_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v := by
  unfold Submodule.localBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem mul_tmul_one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    x * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c' * c, mul_mem hc' hc, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [zero_mul]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, mul_mem hc' hc, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span]
  exact Submodule.subset_span ⟨1, hΛ.one_mem, 1, one_mem _, rfl⟩

theorem tmul_one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span]
  exact Submodule.subset_span ⟨z, hz, 1, one_mem _, rfl⟩

end CSTowerT21.HL

namespace CSTowerT21
namespace IDX

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem relIndex_meetOrder_eq_succ {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓq' : ℓ ≠ q')
    {g : (ℍ𝔸)ˣ} (hg : g ∈ primeHeckeSet R ℓ) :
    (Submodule.finiteIdeleStabilizer (meetOrder R g)).relIndex (Submodule.finiteIdeleStabilizer R) = ℓ + 1 := by
  have hRo : IsOrder R := hR.isOrder
  rw [Stab.finiteIdeleStabilizer_meetOrder_eq hRo g,
    Subgroup.relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq]
  have hset : ∀ c : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer R,
      (∃ k ∈ Submodule.finiteIdeleStabilizer R,
          (QuotientGroup.mk (k * g) : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer R) = c) ↔
        (∃ h ∈ primeHeckeSet R ℓ, (QuotientGroup.mk h : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer R) = c) := by
    intro c
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k * g, HL.mul_mem_primeHeckeSet_of_mem_stabilizer hRo ℓ hk hg, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      rw [QuaternionAlgebra.primeHeckeSet_eq_doubleCoset_finiteIdeleStabilizer hdef hR ℓ hℓN hℓq' hg] at hh
      obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hh
      refine ⟨x, hx, ?_⟩
      rw [QuotientGroup.eq, inv_mul_cancel_left]
      exact hy
  rw [Nat.card_congr (Equiv.subtypeEquivRight hset)]
  exact CerednikDrinfeld.natCard_setOf_exists_mem_primeHeckeSet_quotientMk_eq_eq_succ_of_prime R ℓ hR hℓN hℓq'.symm hdef

end CSTowerT21.IDX

theorem solution
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓq' : ℓ ≠ q')
    {g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hg : g ∈ QuaternionAlgebra.primeHeckeSet R ℓ) :
    (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R g)).relIndex
      (Submodule.finiteIdeleStabilizer R) = ℓ + 1 :=
  CSTowerT21.IDX.relIndex_meetOrder_eq_succ hdef hR ℓ hℓN hℓq' hg

end S_CerednikDrinfeld_relIndex_finiteIdeleStabilizer_meetOrder_eq_succ_of_mem_primeHeckeSet
end P2MW
export P2MW.S_CerednikDrinfeld_relIndex_finiteIdeleStabilizer_meetOrder_eq_succ_of_mem_primeHeckeSet (solution)
