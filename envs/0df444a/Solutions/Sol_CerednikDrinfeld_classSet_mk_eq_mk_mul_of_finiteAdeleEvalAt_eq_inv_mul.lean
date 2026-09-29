-- Prove2me | solution 1 for CerednikDrinfeld.classSet_mk_eq_mk_mul_of_finiteAdeleEvalAt_eq_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/999743a9-9450-5cce-b172-27f20ee94682

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet
import Theorems.Thm_Matrix_GeneralLinearGroup_exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_classSet_mk_eq_mk_mul_of_finiteAdeleEvalAt_eq_inv_mul
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

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

private theorem _root_.CSTowerT21.Stab.mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (u : (ℍ𝔸)ˣ) :
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

p2m_export "CSTowerT21.Stab" "mem_stabilizer_iff"

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

private theorem _root_.CSTowerT21.Stab.one_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) ∈ Submodule.localBoxUnits Λ v := by
  rw [mem_localBoxUnits_iff', inv_one, Units.val_one]
  exact ⟨one_mem_localBox hΛ v, one_mem_localBox hΛ v⟩

p2m_export "CSTowerT21.Stab" "one_mem_localBoxUnits"

theorem mem_stabilizer_iff_forall {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔ ∀ v, (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits Λ v :=
  IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ hΛ u

private theorem _root_.CSTowerT21.Stab.eq_of_natCast_prime_mem {ℓ : ℕ} (hℓ : ℓ.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((ℓ : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  apply Subtype.ext
  show Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator w
  rw [← natGenerator_dvd_iff'] at hv hw
  rw [(Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hv,
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hℓ).mp hw]

p2m_export "CSTowerT21.Stab" "eq_of_natCast_prime_mem"

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
namespace Nat

noncomputable def placesOf (ℓ : ℕ) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  if h : (Ideal.span {(ℓ : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) = ⊥ then ∅ else (Ideal.finite_factors h).toFinset

theorem span_natCast_ne_bot {ℓ : ℕ} (hℓ : ℓ ≠ 0) : (Ideal.span {(ℓ : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hℓ

theorem mem_placesOf_iff {ℓ : ℕ} (hℓ : ℓ ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ placesOf ℓ ↔ (ℓ : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [placesOf, dif_neg (span_natCast_ne_bot hℓ), Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    Ideal.dvd_span_singleton]

theorem inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ placesOf ℓ) :
    algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ := by
  rw [mem_placesOf_iff hℓ] at hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) = v.valuation ℚ ((ℓ : ℚ)⁻¹) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _, map_inv₀]
  have h1 : v.valuation ℚ (ℓ : ℚ) = 1 := by
    have : (ℓ : ℚ) = algebraMap (𝓞 ℚ) ℚ (ℓ : 𝓞 ℚ) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
    have hle := v.intValuation_le_one (ℓ : 𝓞 ℚ)
    have hnlt : ¬ v.intValuation (ℓ : 𝓞 ℚ) < 1 := by
      rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact hv
    exact le_antisymm hle (not_lt.mp hnlt)
  rw [h1, inv_one]

theorem disjoint_placesOf_of_coprime {ℓ ℓ' : ℕ} (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0) (h : ℓ.Coprime ℓ') :
    Disjoint (placesOf ℓ) (placesOf ℓ') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_placesOf_iff hℓ] at hv
  rw [mem_placesOf_iff hℓ'] at hv'
  have hcop : IsCoprime (ℓ : 𝓞 ℚ) (ℓ' : 𝓞 ℚ) := by
    have := (Nat.isCoprime_iff_coprime.mpr h : IsCoprime (ℓ : ℤ) (ℓ' : ℤ))
    simpa using this.map (Int.castRingHom (𝓞 ℚ))
  obtain ⟨x, y, hxy⟩ := hcop
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hxy]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hv) (Ideal.mul_mem_left _ _ hv')

theorem not_mem_placesOf_of_mem_placesOf_of_coprime {ℓ ℓ' : ℕ} (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0) (h : ℓ.Coprime ℓ')
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ placesOf ℓ) : v ∉ placesOf ℓ' :=
  Finset.disjoint_left.mp (disjoint_placesOf_of_coprime hℓ hℓ' h) hv

theorem isMaximal_span_natCast_of_prime {p : ℕ} (hp : p.Prime) :
    (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsMaximal := by
  have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hpZ : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpO : _root_.Prime (p : 𝓞 ℚ) := by
    have : (p : 𝓞 ℚ) = e.symm (p : ℤ) := by rw [map_natCast]
    rw [this]
    exact (MulEquiv.prime_iff (e.symm : ℤ ≃* 𝓞 ℚ)).mpr hpZ
  have hprime : (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsPrime := (Ideal.span_singleton_prime hpO.ne_zero).mpr hpO
  exact hprime.isMaximal (span_natCast_ne_bot hp.ne_zero)

namespace HeightOneSpectrum

private theorem _root_.CSTowerT21.Nat.HeightOneSpectrum.eq_of_natCast_prime_mem {p : ℕ} (hp : p.Prime) {v v' : HeightOneSpectrum (𝓞 ℚ)}
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) (hv' : (p : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' := by
  have hmax := isMaximal_span_natCast_of_prime hp
  have h1 : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)).symm
  have h2 : v'.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v'.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv')).symm
  exact HeightOneSpectrum.ext (h1.trans h2.symm)

end HeightOneSpectrum
p2m_export "CSTowerT21.Nat" "HeightOneSpectrum.eq_of_natCast_prime_mem"
end CSTowerT21.Nat

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

private theorem _root_.CSTowerT21.HL.mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  ⟨fun hu => ⟨coe_mem_box_of_mem_stabilizer hΛ hu, coe_inv_mem_box_of_mem_stabilizer hΛ hu⟩,
   fun h => mem_stabilizer_of_coe_mem_of_coe_inv_mem hΛ h.1 h.2⟩

p2m_export "CSTowerT21.HL" "mem_stabilizer_iff"

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
namespace C4T

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

open CSTowerT21.HL

theorem mul_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    {u u' : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ} (hu : u ∈ Submodule.localBoxUnits Λ w) (hu' : u' ∈ Submodule.localBoxUnits Λ w) :
    u * u' ∈ Submodule.localBoxUnits Λ w := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul]; exact localBox_mul_mem hΛ w hu.1 hu'.1
  · rw [mul_inv_rev, Units.val_mul]; exact localBox_mul_mem hΛ w hu'.2 hu.2

theorem inv_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (w : HeightOneSpectrum (𝓞 ℚ))
    {u : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ} (hu : u ∈ Submodule.localBoxUnits Λ w) : u⁻¹ ∈ Submodule.localBoxUnits Λ w :=
  ⟨hu.2, by rw [inv_inv]; exact hu.1⟩

theorem one_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) ∈ Submodule.localBoxUnits Λ w :=
  ⟨by rw [Units.val_one]; exact one_mem_localBox hΛ w, by rw [inv_one, Units.val_one]; exact one_mem_localBox hΛ w⟩

theorem mem_stabilizer_localBox_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
    g ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) ↔
      g ∈ Submodule.localBoxUnits Λ w := by
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) := inv_mem hg
    rw [MulAction.mem_stabilizer_iff] at hg hg'
    refine ⟨?_, ?_⟩
    · have h1 : (g : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * 1 ∈ g • ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) :=
        Set.smul_mem_smul_set (one_mem_localBox hΛ w)
      rw [hg, mul_one] at h1; exact h1
    · have h1 : ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * 1 ∈ g⁻¹ • ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) :=
        Set.smul_mem_smul_set (one_mem_localBox hΛ w)
      rw [hg', mul_one] at h1; exact h1
  · rintro ⟨h1, h2⟩
    rw [MulAction.mem_stabilizer_iff]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact localBox_mul_mem hΛ w h1 hx
    · intro x hx
      refine ⟨(g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) • x, localBox_mul_mem hΛ w h2 hx, ?_⟩
      show (g : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * (((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * x) = x
      rw [← mul_assoc, Units.mul_inv, one_mul]

theorem finiteAdeleEvalAt_smul (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ𝔸) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (c • x) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c) * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x := by
  rw [map_smul, ← Algebra.TensorProduct.algebraMap_apply', ← Algebra.smul_def]
  try rfl

theorem natCast_smul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (w : HeightOneSpectrum (𝓞 ℚ)) (q : ℕ)
    {y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hy : y ∈ Submodule.localBox Λ w) : (q : ℚ) • y ∈ Submodule.localBox Λ w := by
  rw [Nat.cast_smul_eq_nsmul ℚ]; exact AddSubgroup.nsmul_mem _ hy q

theorem inv_natCast_integral_of_ne {q : ℕ} (hq : q.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : w ≠ v) :
    algebraMap ℚ (w.adicCompletion ℚ) ((q : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ := by
  apply Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hq.ne_zero
  intro hmem
  rw [Nat.mem_placesOf_iff hq.ne_zero] at hmem
  exact hw (Nat.HeightOneSpectrum.eq_of_natCast_prime_mem hq hmem hqv)

theorem exists_natCast_mem_asIdeal {q : ℕ} (hq : q.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
  ⟨⟨Ideal.span {(q : 𝓞 ℚ)}, (Nat.isMaximal_span_natCast_of_prime hq).isPrime, Nat.span_natCast_ne_bot hq.ne_zero⟩,
    Ideal.mem_span_singleton_self _⟩

def OffUnit (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (h : (ℍ𝔸)ˣ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom h ∈ Submodule.localBoxUnits Λ w

theorem offUnit_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} (hq : q.Prime)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    {h : (ℍ𝔸)ˣ} (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ q) : OffUnit Λ v h :=
  fun w hw => map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet q hh w (inv_natCast_integral_of_ne hq hqv hw)

theorem exists_offUnit_map_eq {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    ∃ β : (ℍ𝔸)ˣ, Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom β = g ∧ OffUnit Λ v β := by
  classical
  obtain ⟨β, h1, h2⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) {v}
    (Function.update (fun w : HeightOneSpectrum (𝓞 ℚ) => (1 : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ)) v g)
  have h1v := h1 v (Finset.mem_singleton_self v)
  rw [Function.update_self] at h1v
  refine ⟨β, Units.ext h1v, fun w hw => ?_⟩
  have e : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom β = 1 := Units.ext (h2 w (fun hmem => hw (Finset.mem_singleton.mp hmem)))
  rw [e]; exact one_mem_localBoxUnits hΛ w

theorem mem_box_iff_local {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : QuaternionAlgebra.IsOrder X) (v : HeightOneSpectrum (𝓞 ℚ))
    {x : ℍ𝔸} (hx : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x ∈ Submodule.localBox X w) :
    x ∈ Submodule.finiteAdeleBox X ↔ Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v x ∈ Submodule.localBox X v := by
  rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox X hX.fg hX.spanTop]
  refine ⟨fun h => h v, fun h w => ?_⟩
  by_cases hw : w = v
  · subst hw; exact h
  · exact hx w hw

def locT (R : Submodule ℤ ℍ[ℚ, a, b]) (q : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ :=
  {g |
        ((g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
          (q : ℚ) • ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
          ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v ∧
          (q : ℚ)⁻¹ • (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v)}

theorem mem_primeHeckeSet_iff_local {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R) {q : ℕ} (hq : q.Prime)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) {h : (ℍ𝔸)ˣ} (hoff : OffUnit R v h) :
    h ∈ QuaternionAlgebra.primeHeckeSet R q ↔ Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h ∈ locT R q v := by
  have off1 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (h : ℍ𝔸) ∈ Submodule.localBox R w :=
    fun w hw => (hoff w hw).1
  have off2 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R w :=
    fun w hw => (hoff w hw).2
  have off3 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((q : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈ Submodule.localBox R w :=
    fun w hw => by rw [map_smul]; exact natCast_smul_mem_localBox w q (off2 w hw)
  have off4 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((q : ℚ)⁻¹ • (h : ℍ𝔸)) ∈ Submodule.localBox R w :=
    fun w hw => by
      rw [finiteAdeleEvalAt_smul]
      exact tmul_one_mul_mem_localBox w (inv_natCast_integral_of_ne hq hqv hw) (off1 w hw)
  rw [QuaternionAlgebra.mem_primeHeckeSet_iff, mem_box_iff_local hRo v off1, mem_box_iff_local hRo v off3,
    mem_box_iff_local hRo v off2, mem_box_iff_local hRo v off4, map_smul, map_smul]
  exact Iff.rfl

theorem map_mem_stabilizer_of_mem_finiteIdeleStabilizer {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R)
    (v : HeightOneSpectrum (𝓞 ℚ)) {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer R) :
    Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom u ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) := by
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits _ hRo] at hu
  exact (mem_stabilizer_localBox_iff hRo v _).mpr (hu v)

theorem inv_mul_mem_finiteIdeleStabilizer_of_local {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R)
    {v : HeightOneSpectrum (𝓞 ℚ)} {h h' : (ℍ𝔸)ˣ} (hoff : OffUnit R v h) (hoff' : OffUnit R v h')
    (hK : (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h)⁻¹ * Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h' ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))) :
    h⁻¹ * h' ∈ Submodule.finiteIdeleStabilizer R := by
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits _ hRo]
  intro w
  rw [map_mul, map_inv]
  by_cases hw : w = v
  · subst hw; exact (mem_stabilizer_localBox_iff hRo _ _).mp hK
  · exact mul_mem_localBoxUnits hRo w (inv_mem_localBoxUnits w (hoff w hw)) (hoff' w hw)

end CSTowerT21.C4T

open QuaternionAlgebra CerednikDrinfeld in
theorem solution
    {a b : ℚ} (O : Submodule ℤ ℍ[ℚ, a, b]) (hO : QuaternionAlgebra.IsOrder O)
    (q : ℕ) [Fact q.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (s : (ℍ[ℚ, a, b])ˣ) (sf : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hsf : ∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (sf : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ))
    (hsfv : ∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ u.asIdeal → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (sf : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (x y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hx : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hy : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hyv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] s)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer O) y =
      QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer O) (x * sf) := by
  have hne : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal :=
    fun u hu h => hu (CSTowerT21.Stab.eq_of_natCast_prime_mem (Fact.out : q.Prime) h hv)
  set g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] s with hg
  set t : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := (x * sf)⁻¹ * (g * y) with ht
  have E1 : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ), Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 →
      CSTowerT21.Stab.evU (a := a) (b := b) w u = 1 := fun w u h => Units.ext (by simpa [CSTowerT21.Stab.evU] using h)
  have hgw : ∀ w : HeightOneSpectrum (𝓞 ℚ), Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
    intro w; rw [hg, Submodule.val_finiteIdeleDiagonal_apply, Submodule.finiteAdeleEvalAt_tmul]; rfl
  have Esf : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → CSTowerT21.Stab.evU (a := a) (b := b) w sf = CSTowerT21.Stab.evU (a := a) (b := b) w g :=
    fun w hw => Units.ext (by
      change Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (sf : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
      rw [hsf w (hne w hw), hgw])
  have hyv' : CSTowerT21.Stab.evU (a := a) (b := b) v y = (CSTowerT21.Stab.evU (a := a) (b := b) v g)⁻¹ * CSTowerT21.Stab.evU (a := a) (b := b) v x := by
    apply Units.ext
    rw [Units.val_mul, ← map_inv]
    simpa [CSTowerT21.Stab.evU] using hyv
  have htU : t ∈ Submodule.finiteIdeleStabilizer O := by
    rw [IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits O hO]
    intro w
    change CSTowerT21.Stab.evU (a := a) (b := b) w t ∈ Submodule.localBoxUnits O w
    rw [ht, map_mul, map_mul, map_inv, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [hyv', E1 w sf (hsfv w hv)]
      have e : (CSTowerT21.Stab.evU (a := a) (b := b) w x * 1)⁻¹ *
          (CSTowerT21.Stab.evU (a := a) (b := b) w g * ((CSTowerT21.Stab.evU (a := a) (b := b) w g)⁻¹ * CSTowerT21.Stab.evU (a := a) (b := b) w x)) = 1 := by group
      rw [e]
      exact CSTowerT21.C4T.one_mem_localBoxUnits hO w
    · rw [E1 w x (hx w hw), E1 w y (hy w hw), Esf w hw]
      have e : (1 * CSTowerT21.Stab.evU (a := a) (b := b) w g)⁻¹ * (CSTowerT21.Stab.evU (a := a) (b := b) w g * 1) = 1 := by group
      rw [e]
      exact CSTowerT21.C4T.one_mem_localBoxUnits hO w
  have e : y = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] s⁻¹ * (x * sf * t) := by
    rw [ht, map_inv, hg]; group
  rw [e, QuaternionAlgebra.ClassSet.mk_diagonal_mul, QuaternionAlgebra.ClassSet.mk_mul_of_mem _ _ htU]

end S_CerednikDrinfeld_classSet_mk_eq_mk_mul_of_finiteAdeleEvalAt_eq_inv_mul
end P2MW
export P2MW.S_CerednikDrinfeld_classSet_mk_eq_mk_mul_of_finiteAdeleEvalAt_eq_inv_mul (solution)
