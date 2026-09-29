-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.mul_self_mem_level_and_not_mem_level_and_mem_inf_conj_iff_of_mem_primeHeckeSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/94c966d7-037d-5b86-a1ad-0fed44f2d787

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_mul_self_mem_level_and_not_mem_level_and_mem_inf_conj_iff_of_mem_primeHeckeSet
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false
open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

noncomputable section

namespace LocalAL

variable {a b : ℚ}

theorem natCast_not_mem_asIdeal_of_coprime {m k : ℕ} (h : m.Coprime k) (v : HeightOneSpectrum (𝓞 ℚ))
    (hm : (m : 𝓞 ℚ) ∈ v.asIdeal) : (k : 𝓞 ℚ) ∉ v.asIdeal := by
  intro hk
  have hcop : IsCoprime (m : 𝓞 ℚ) (k : 𝓞 ℚ) := by
    have := (Nat.isCoprime_iff_coprime.mpr h : IsCoprime (m : ℤ) (k : ℤ))
    simpa using this.map (Int.castRingHom (𝓞 ℚ))
  obtain ⟨x, y, hxy⟩ := hcop
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hxy]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hk)

theorem valuation_natCast_lt_one {p : ℕ} (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    Valued.v ((p : ℕ) : v.adicCompletion ℚ) < 1 := by
  have e : ((p : ℕ) : v.adicCompletion ℚ) = algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ) := by
    rw [map_natCast]
  have hval : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) = v.valuation ℚ (p : ℚ) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have e2 : (p : ℚ) = algebraMap (𝓞 ℚ) ℚ (p : 𝓞 ℚ) := by simp
  rw [e, hval, e2, HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).mpr hpv

theorem natCast_ne_zero_adicCompletion {p : ℕ} (hp : p ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((p : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ))]
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hp)

theorem inv_natCast_not_mem_adicCompletionIntegers {p : ℕ} (hp : p ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    ((p : ℕ) : v.adicCompletion ℚ)⁻¹ ∉ v.adicCompletionIntegers ℚ := by
  intro h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀] at h
  have hlt := valuation_natCast_lt_one v hpv
  have hne : Valued.v ((p : ℕ) : v.adicCompletion ℚ) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (natCast_ne_zero_adicCompletion hp v)
  have h1 : (1 : _) ≤ Valued.v ((p : ℕ) : v.adicCompletion ℚ) := (inv_le_one₀ (zero_lt_iff.mpr hne)).mp h
  exact absurd (lt_of_lt_of_le hlt h1) (lt_irrefl _)

theorem mem_and_inv_mem_of_sq (v : HeightOneSpectrum (𝓞 ℚ)) {x : v.adicCompletion ℚ} (hx : x ≠ 0)
    (h1 : x ^ 2 ∈ v.adicCompletionIntegers ℚ) (h2 : (x ^ 2)⁻¹ ∈ v.adicCompletionIntegers ℚ) :
    x ∈ v.adicCompletionIntegers ℚ ∧ x⁻¹ ∈ v.adicCompletionIntegers ℚ := by
  rcases (v.adicCompletionIntegers ℚ).mem_or_inv_mem x with h | h
  · refine ⟨h, ?_⟩
    have e : x⁻¹ = x * (x ^ 2)⁻¹ := by field_simp
    rw [e]; exact mul_mem h h2
  · refine ⟨?_, h⟩
    have e : x = x⁻¹ * x ^ 2 := by field_simp
    rw [e]; exact mul_mem h h1

theorem localBox_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v := by
  unfold Submodule.localBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem one_tmul_mul_comm (v : HeightOneSpectrum (𝓞 ℚ)) (c : v.adicCompletion ℚ) (x : CosetGraph.Loc a b v) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x = x * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [mul_zero, zero_mul]
  | tmul y d =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_comm]
  | add y z hy hz => rw [mul_add, add_mul, hy, hz]

abbrev scalarU (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ) : (CosetGraph.Loc a b v)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℍ[ℚ, a, b]) (B := v.adicCompletion ℚ)).toRingHom.toMonoidHom c

theorem val_scalarU (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ) :
    ((scalarU (a := a) (b := b) v c : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) =
      (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (c : v.adicCompletion ℚ) := rfl

theorem val_scalarU_inv (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ) :
    (((scalarU (a := a) (b := b) v c)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) =
      (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := rfl

theorem scalarU_mem_scalarUnits (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ) :
    scalarU (a := a) (b := b) v c ∈ CosetGraph.scalarUnits v := ⟨c, rfl⟩

theorem conj_scalarU (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ) (g : (CosetGraph.Loc a b v)ˣ) :
    g⁻¹ * scalarU v c * g = scalarU v c := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_scalarU, mul_assoc, one_tmul_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

theorem mem_level_of_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    (c : (v.adicCompletion ℚ)ˣ) {k : (CosetGraph.Loc a b v)ˣ}
    (hu : (scalarU v c)⁻¹ * k ∈ Submodule.localBoxUnits Λ v) : k ∈ CosetGraph.level Λ v := by
  have e : k = scalarU v c * ((scalarU v c)⁻¹ * k) := by rw [mul_inv_cancel_left]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (scalarU_mem_scalarUnits v c))
    (Subgroup.mem_sup_left (Subgroup.subset_closure hu))

abbrev nU (v : HeightOneSpectrum (𝓞 ℚ)) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (CosetGraph.Loc a b v)ˣ :=
  Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n

theorem val_nU (v : HeightOneSpectrum (𝓞 ℚ)) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((nU v n : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) =
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (n : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl

theorem val_nU_inv (v : HeightOneSpectrum (𝓞 ℚ)) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) =
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((n⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl

theorem isOrder_meetOrder {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : IsOrder (meetOrder R n) :=
  hRo.inf (IsOrder.conjByFiniteIdele R hRo n)

theorem mem_localBox_meetOrder_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (x : CosetGraph.Loc a b v) :
    x ∈ Submodule.localBox (meetOrder R n) v ↔
      x ∈ Submodule.localBox R v ∧
        (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) * x * (nU v n : (CosetGraph.Loc a b v)ˣ) ∈
          Submodule.localBox R v := by
  have hC : IsOrder (Submodule.conjByFiniteIdele R n) := IsOrder.conjByFiniteIdele R hRo n
  show x ∈ Submodule.localBox (R ⊓ Submodule.conjByFiniteIdele R n) v ↔ _
  rw [Submodule.localBox_inf R _ hRo.fg hRo.spanTop hC.fg hC.spanTop v, AddSubgroup.mem_inf,
    Submodule.mem_localBox_conjByFiniteIdele_iff R hRo.fg hRo.spanTop n v x]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    rw [← val_nU, ← val_nU_inv, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← val_nU, ← val_nU_inv, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

theorem conj_mem_localBox_of_conjByFiniteIdele_eq {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (v : HeightOneSpectrum (𝓞 ℚ)) {y : CosetGraph.Loc a b v} (hy : y ∈ Submodule.localBox (meetOrder R n) v) :
    (nU v n : (CosetGraph.Loc a b v)ˣ) * y * (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) ∈
      Submodule.localBox R v := by
  have hS : IsOrder (meetOrder R n) := isOrder_meetOrder hRo n
  have h1 : (nU v n : (CosetGraph.Loc a b v)ˣ) * y * (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) ∈
      Submodule.localBox (Submodule.conjByFiniteIdele (meetOrder R n) n) v :=
    (Submodule.mem_localBox_conjByFiniteIdele_iff _ hS.fg hS.spanTop n v _).mpr ⟨y, hy, rfl⟩
  rw [hnorm] at h1
  exact localBox_mono (inf_le_left : meetOrder R n ≤ R) v h1

section Frame

variable (v : HeightOneSpectrum (𝓞 ℚ))

def IsInt (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) : Prop :=
  ∀ i j, M i j ∈ v.adicCompletionIntegers ℚ

variable {v}

theorem IsInt.mul {A B : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)} (hA : IsInt v A) (hB : IsInt v B) :
    IsInt v (A * B) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem (mul_mem (hA i 0) (hB 0 j)) (mul_mem (hA i 1) (hB 1 j))

theorem IsInt.one : IsInt v (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem IsInt.smul {A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)} (hA : IsInt v A) {c : v.adicCompletion ℚ}
    (hc : c ∈ v.adicCompletionIntegers ℚ) : IsInt v (c • A) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_mem hc (hA i j)

theorem IsInt.det {A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)} (hA : IsInt v A) :
    A.det ∈ v.adicCompletionIntegers ℚ := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hA 0 0) (hA 1 1)) (mul_mem (hA 0 1) (hA 1 0))

variable (v) in

def scalGL (φ : CosetGraph.Loc a b v ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    Subgroup (CosetGraph.Loc a b v)ˣ where
  carrier := {k | ∃ c : v.adicCompletion ℚ, c ≠ 0 ∧ IsInt v (c⁻¹ • φ (k : CosetGraph.Loc a b v)) ∧
    IsInt v (c • φ ((k⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v))}
  one_mem' := by
    refine ⟨1, one_ne_zero, ?_, ?_⟩
    · rw [inv_one, one_smul, Units.val_one, map_one]; exact IsInt.one
    · rw [one_smul, inv_one, Units.val_one, map_one]; exact IsInt.one
  mul_mem' := by
    rintro x y ⟨c, hc, hx1, hx2⟩ ⟨d, hd, hy1, hy2⟩
    refine ⟨c * d, mul_ne_zero hc hd, ?_, ?_⟩
    · rw [Units.val_mul, map_mul, mul_inv, ← smul_mul_smul_comm]; exact hx1.mul hy1
    · rw [mul_inv_rev, Units.val_mul, map_mul, mul_comm c d, ← smul_mul_smul_comm]; exact hy2.mul hx2
  inv_mem' := by
    rintro x ⟨c, hc, hx1, hx2⟩
    refine ⟨c⁻¹, inv_ne_zero hc, ?_, ?_⟩
    · rw [inv_inv]; exact hx2
    · rw [inv_inv]; exact hx1

variable {R : Submodule ℤ ℍ[ℚ, a, b]}
  {φ : CosetGraph.Loc a b v ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}

theorem level_le_scalGL
    (hφ1 : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hφR : ∀ x : CosetGraph.Loc a b v, x ∈ Submodule.localBox R v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ) :
    CosetGraph.level R v ≤ scalGL v φ := by
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le]
    intro u hu
    refine ⟨1, one_ne_zero, ?_, ?_⟩
    · rw [inv_one, one_smul]; exact (hφR _).mp hu.1
    · rw [one_smul]; exact (hφR _).mp hu.2
  · rintro _ ⟨c, rfl⟩
    refine ⟨(c : v.adicCompletion ℚ), c.ne_zero, ?_, ?_⟩
    · show IsInt v ((c : v.adicCompletion ℚ)⁻¹ • φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (c : v.adicCompletion ℚ)))
      rw [hφ1, smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul]; exact IsInt.one
    · show IsInt v ((c : v.adicCompletion ℚ) • φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)))
      rw [hφ1, smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ c.ne_zero, one_smul]; exact IsInt.one

theorem mem_level_of_isInt
    (hφ1 : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hφR : ∀ x : CosetGraph.Loc a b v, x ∈ Submodule.localBox R v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ)
    {k : (CosetGraph.Loc a b v)ˣ} {c : v.adicCompletion ℚ} (hc : c ≠ 0)
    (h1 : IsInt v (c⁻¹ • φ (k : CosetGraph.Loc a b v)))
    (h2 : IsInt v (c • φ ((k⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v))) :
    k ∈ CosetGraph.level R v := by
  refine mem_level_of_localBoxUnits v (Units.mk0 c hc) ⟨?_, ?_⟩
  · show ((((scalarU v (Units.mk0 c hc))⁻¹ * k : (CosetGraph.Loc a b v)ˣ)) : CosetGraph.Loc a b v) ∈ Submodule.localBox R v
    rw [hφR, Units.val_mul, map_mul, val_scalarU_inv, hφ1, smul_one_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    exact h1
  · show ((((scalarU v (Units.mk0 c hc))⁻¹ * k)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) ∈ Submodule.localBox R v
    rw [hφR, mul_inv_rev, inv_inv, Units.val_mul, map_mul, val_scalarU, hφ1, mul_smul_one, Units.val_mk0]
    exact h2

end Frame

section Core

variable {v : HeightOneSpectrum (𝓞 ℚ)} {R : Submodule ℤ ℍ[ℚ, a, b]}
  {n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} {p : ℕ}
  {φ : CosetGraph.Loc a b v ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
  {k₀ k₀i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}

theorem D_eq (c : v.adicCompletion ℚ) :
    !![(1 : v.adicCompletion ℚ), 0; 0, c] = Matrix.diagonal ![(1 : v.adicCompletion ℚ), c] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem isInt_of_entries {c₀₀ c₀₁ c₁₀ c₁₁ : v.adicCompletion ℚ}
    (h₀₀ : c₀₀ ∈ v.adicCompletionIntegers ℚ) (h₀₁ : c₀₁ ∈ v.adicCompletionIntegers ℚ)
    (h₁₀ : c₁₀ ∈ v.adicCompletionIntegers ℚ) (h₁₁ : c₁₁ ∈ v.adicCompletionIntegers ℚ) :
    IsInt v !![c₀₀, c₀₁; c₁₀, c₁₁] := by
  intro i j; fin_cases i <;> fin_cases j <;> simpa

theorem isInt_conj_of_test
    (hφR : ∀ x : CosetGraph.Loc a b v, x ∈ Submodule.localBox R v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ)
    (hSv : ∀ x : CosetGraph.Loc a b v, x ∈ Submodule.localBox (meetOrder R n) v ↔
      x ∈ Submodule.localBox R v ∧
        (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) * x * (nU v n : (CosetGraph.Loc a b v)ˣ) ∈
          Submodule.localBox R v)
    (hconj : ∀ y ∈ Submodule.localBox (meetOrder R n) v,
      (nU v n : (CosetGraph.Loc a b v)ˣ) * y * (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) ∈
        Submodule.localBox R v)
    (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (hY : IsInt v Y)
    (hY' : IsInt v (φ (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) * Y *
      φ ((nU v n : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v))) :
    IsInt v (φ ((nU v n : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) * Y *
      φ (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v)) := by
  have hy : φ.symm Y ∈ Submodule.localBox (meetOrder R n) v := by
    rw [hSv]
    refine ⟨(hφR _).mpr ?_, (hφR _).mpr ?_⟩
    · rw [RingEquiv.apply_symm_apply]; exact hY
    · rw [map_mul, map_mul, RingEquiv.apply_symm_apply]; exact hY'
  have h := (hφR _).mp (hconj _ hy)
  rw [map_mul, map_mul, RingEquiv.apply_symm_apply] at h
  exact h

theorem entry01_mem
    (hφR : ∀ x : CosetGraph.Loc a b v, x ∈ Submodule.localBox R v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ)
    (hSv : ∀ x : CosetGraph.Loc a b v, x ∈ Submodule.localBox (meetOrder R n) v ↔
      x ∈ Submodule.localBox R v ∧
        (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) * x * (nU v n : (CosetGraph.Loc a b v)ˣ) ∈
          Submodule.localBox R v)
    (hconj : ∀ y ∈ Submodule.localBox (meetOrder R n) v,
      (nU v n : (CosetGraph.Loc a b v)ˣ) * y * (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) ∈
        Submodule.localBox R v)
    (hk₀ : IsInt v k₀) (hk₀i : IsInt v k₀i)
    (hn1 : φ ((nU v n : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) =
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] * k₀)
    (hn2 : φ (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) =
      k₀i * Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹])
    (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (hY : IsInt v Y)
    (hDY : IsInt v (Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹] * Y *
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)])) :
    (k₀ * Y * k₀i) 0 1 * (p : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
  have hY' : IsInt v (φ (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) * Y *
      φ ((nU v n : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v)) := by
    rw [hn1, hn2]
    have e : k₀i * Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹] * Y *
        (Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] * k₀) =
        k₀i * (Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹] * Y *
          Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)]) * k₀ := by
      simp only [Matrix.mul_assoc]
    rw [e]
    exact (hk₀i.mul hDY).mul hk₀
  have h := isInt_conj_of_test hφR hSv hconj Y hY hY' 0 1
  rw [hn1, hn2] at h
  have e : Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] * k₀ * Y *
      (k₀i * Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹]) =
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] *
        ((k₀ * Y * k₀i) * Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹]) := by
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.diagonal_mul, Matrix.mul_diagonal] at h
  simpa using h

theorem key_entries (hp0 : (p : v.adicCompletion ℚ) ≠ 0)
    (hφR : ∀ x : CosetGraph.Loc a b v, x ∈ Submodule.localBox R v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ)
    (hSv : ∀ x : CosetGraph.Loc a b v, x ∈ Submodule.localBox (meetOrder R n) v ↔
      x ∈ Submodule.localBox R v ∧
        (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) * x * (nU v n : (CosetGraph.Loc a b v)ˣ) ∈
          Submodule.localBox R v)
    (hconj : ∀ y ∈ Submodule.localBox (meetOrder R n) v,
      (nU v n : (CosetGraph.Loc a b v)ˣ) * y * (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) ∈
        Submodule.localBox R v)
    (hk₀ : IsInt v k₀) (hk₀i : IsInt v k₀i) (h1 : k₀ * k₀i = 1)
    (hn1 : φ ((nU v n : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) =
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] * k₀)
    (hn2 : φ (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) =
      k₀i * Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹]) :
    (p : v.adicCompletion ℚ)⁻¹ * k₀ 0 0 ∈ v.adicCompletionIntegers ℚ ∧
      (p : v.adicCompletion ℚ)⁻¹ * k₀i 1 1 ∈ v.adicCompletionIntegers ℚ := by
  have hpO : (p : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := natCast_mem _ _

  have hE00 : IsInt v !![(1 : v.adicCompletion ℚ), 0; 0, 0] :=
    isInt_of_entries (one_mem _) (zero_mem _) (zero_mem _) (zero_mem _)
  have hE01 : IsInt v !![(0 : v.adicCompletion ℚ), 1; 0, 0] :=
    isInt_of_entries (zero_mem _) (one_mem _) (zero_mem _) (zero_mem _)
  have hE11 : IsInt v !![(0 : v.adicCompletion ℚ), 0; 0, 1] :=
    isInt_of_entries (zero_mem _) (zero_mem _) (zero_mem _) (one_mem _)
  have cE00 : Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹] * !![(1 : v.adicCompletion ℚ), 0; 0, 0] *
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] = !![(1 : v.adicCompletion ℚ), 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have cE01 : Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹] * !![(0 : v.adicCompletion ℚ), 1; 0, 0] *
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] = !![(0 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ); 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have cE11 : Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹] * !![(0 : v.adicCompletion ℚ), 0; 0, 1] *
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] = !![(0 : v.adicCompletion ℚ), 0; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hp0]
  have t00 := entry01_mem hφR hSv hconj hk₀ hk₀i hn1 hn2 _ hE00 (by rw [cE00]; exact hE00)
  have t01 := entry01_mem hφR hSv hconj hk₀ hk₀i hn1 hn2 _ hE01
    (by rw [cE01]; exact isInt_of_entries (zero_mem _) hpO (zero_mem _) (zero_mem _))
  have t11 := entry01_mem hφR hSv hconj hk₀ hk₀i hn1 hn2 _ hE11 (by rw [cE11]; exact hE11)
  have e00 : (k₀ * !![(1 : v.adicCompletion ℚ), 0; 0, 0] * k₀i) 0 1 = k₀ 0 0 * k₀i 0 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (k₀ * !![(0 : v.adicCompletion ℚ), 1; 0, 0] * k₀i) 0 1 = k₀ 0 0 * k₀i 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (k₀ * !![(0 : v.adicCompletion ℚ), 0; 0, 1] * k₀i) 0 1 = k₀ 0 1 * k₀i 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e00] at t00; rw [e01] at t01; rw [e11] at t11

  have u11 : k₀ 1 0 * k₀i 0 1 + k₀ 1 1 * k₀i 1 1 = 1 := by
    have := congrFun (congrFun h1 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have u00 : k₀ 0 0 * k₀i 0 0 + k₀ 0 1 * k₀i 1 0 = 1 := by
    have := congrFun (congrFun h1 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  refine ⟨?_, ?_⟩
  · have e : (p : v.adicCompletion ℚ)⁻¹ * k₀ 0 0 =
        (k₀ 0 0 * k₀i 0 1 * (p : v.adicCompletion ℚ)⁻¹) * k₀ 1 0 +
          (k₀ 0 0 * k₀i 1 1 * (p : v.adicCompletion ℚ)⁻¹) * k₀ 1 1 := by
      calc (p : v.adicCompletion ℚ)⁻¹ * k₀ 0 0
          = (p : v.adicCompletion ℚ)⁻¹ * k₀ 0 0 * (k₀ 1 0 * k₀i 0 1 + k₀ 1 1 * k₀i 1 1) := by rw [u11, mul_one]
        _ = _ := by ring
    rw [e]
    exact add_mem (mul_mem t00 (hk₀ 1 0)) (mul_mem t01 (hk₀ 1 1))
  · have e : (p : v.adicCompletion ℚ)⁻¹ * k₀i 1 1 =
        k₀i 0 0 * (k₀ 0 0 * k₀i 1 1 * (p : v.adicCompletion ℚ)⁻¹) +
          k₀i 1 0 * (k₀ 0 1 * k₀i 1 1 * (p : v.adicCompletion ℚ)⁻¹) := by
      calc (p : v.adicCompletion ℚ)⁻¹ * k₀i 1 1
          = (p : v.adicCompletion ℚ)⁻¹ * k₀i 1 1 * (k₀ 0 0 * k₀i 0 0 + k₀ 0 1 * k₀i 1 0) := by rw [u00, mul_one]
        _ = _ := by ring
    rw [e]
    exact add_mem (mul_mem (hk₀i 0 0) t01) (mul_mem (hk₀i 1 0) t11)

theorem isInt_sq (hp0 : (p : v.adicCompletion ℚ) ≠ 0)
    (hk₀ : IsInt v k₀) (hk₀i : IsInt v k₀i)
    (hs : (p : v.adicCompletion ℚ)⁻¹ * k₀ 0 0 ∈ v.adicCompletionIntegers ℚ)
    (hz : (p : v.adicCompletion ℚ)⁻¹ * k₀i 1 1 ∈ v.adicCompletionIntegers ℚ)
    (hn1 : φ ((nU v n : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) =
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] * k₀)
    (hn2 : φ (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) =
      k₀i * Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹]) :
    IsInt v ((p : v.adicCompletion ℚ)⁻¹ • φ ((nU v n * nU v n : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v)) ∧
      IsInt v ((p : v.adicCompletion ℚ) • φ (((nU v n * nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v)) := by
  have hpO : (p : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := natCast_mem _ _
  set D := Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] with hD
  set D' := Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹] with hD'
  have hK₁ : IsInt v ((p : v.adicCompletion ℚ)⁻¹ • (D * k₀ * D)) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, hD, Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j
    · simpa using hs
    · convert hk₀ 0 1 using 1; simp; field_simp
    · convert hk₀ 1 0 using 1; simp; field_simp
    · convert mul_mem hpO (hk₀ 1 1) using 1; simp; field_simp
  have hK₂ : IsInt v ((p : v.adicCompletion ℚ) • (D' * k₀i * D')) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, hD', Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j
    · convert mul_mem hpO (hk₀i 0 0) using 1; simp
    · convert hk₀i 0 1 using 1; simp; field_simp
    · convert hk₀i 1 0 using 1; simp; field_simp
    · convert hz using 1; simp; field_simp
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, map_mul, hn1]
    have e : (p : v.adicCompletion ℚ)⁻¹ • (D * k₀ * (D * k₀)) = ((p : v.adicCompletion ℚ)⁻¹ • (D * k₀ * D)) * k₀ := by
      rw [smul_mul_assoc]; simp only [Matrix.mul_assoc]
    rw [e]; exact hK₁.mul hk₀
  · rw [mul_inv_rev, Units.val_mul, map_mul, hn2]
    have e : (p : v.adicCompletion ℚ) • (k₀i * D' * (k₀i * D')) = k₀i * ((p : v.adicCompletion ℚ) • (D' * k₀i * D')) := by
      rw [mul_smul_comm]; simp only [Matrix.mul_assoc]
    rw [e]; exact hk₀i.mul hK₂

theorem not_mem_scalGL (hp : p ≠ 0) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (hk₀ : IsInt v k₀) (hk₀i : IsInt v k₀i) (h1 : k₀ * k₀i = 1)
    (hn1 : φ ((nU v n : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) =
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] * k₀)
    (hn2 : φ (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) =
      k₀i * Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹]) :
    nU v n ∉ scalGL v φ := by
  rintro ⟨c, hc, hA, hB⟩
  rw [hn1] at hA; rw [hn2] at hB
  have i1 := (hA.mul hk₀i) 0 0
  have eA : (c⁻¹ • (Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] * k₀) * k₀i) =
      c⁻¹ • Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] := by
    rw [smul_mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [eA, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq] at i1
  have i2 := (hk₀.mul hB) 1 1
  have eB : k₀ * (c • (k₀i * Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹])) =
      c • Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹] := by
    rw [mul_smul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [eB, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq] at i2
  have h := mul_mem i1 i2
  have e : c⁻¹ * ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)] 0 *
      (c * ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)⁻¹] 1) = (p : v.adicCompletion ℚ)⁻¹ := by
    simp; field_simp
  rw [e] at h
  exact inv_natCast_not_mem_adicCompletionIntegers hp v hpv h

end Core

section Clauses

variable {v : HeightOneSpectrum (𝓞 ℚ)} {R : Submodule ℤ ℍ[ℚ, a, b]}
  {n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
  {φ : CosetGraph.Loc a b v ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}

theorem mem_and_conj_mem_of_mem_level_meetOrder (hRo : IsOrder R)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    {k : (CosetGraph.Loc a b v)ˣ} (hk : k ∈ CosetGraph.level (meetOrder R n) v) :
    k ∈ CosetGraph.level R v ∧ (nU v n)⁻¹ * k * nU v n ∈ CosetGraph.level R v := by
  have hSv := mem_localBox_meetOrder_iff hRo n v
  suffices H : CosetGraph.level (meetOrder R n) v ≤
      CosetGraph.level R v ⊓ (CosetGraph.level R v).comap (MulAut.conj (nU v n)⁻¹).toMonoidHom by
    have h := H hk
    rw [Subgroup.mem_inf, Subgroup.mem_comap] at h
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h2
    exact h2
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le]
    intro u hu
    have hu1 := (hSv _).mp hu.1
    have hu2 := (hSv _).mp hu.2
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (Subgroup.subset_closure ⟨hu1.1, hu2.1⟩), ?_⟩
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.mem_sup_left (Subgroup.subset_closure ⟨?_, ?_⟩)
    · show (((nU v n)⁻¹ * u * nU v n : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) ∈ Submodule.localBox R v
      rw [Units.val_mul, Units.val_mul]; exact hu1.2
    · show ((((nU v n)⁻¹ * u * nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) ∈ Submodule.localBox R v
      rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul]; exact hu2.2
  · rintro _ ⟨c, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right ⟨c, rfl⟩, ?_⟩
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    show (nU v n)⁻¹ * scalarU v c * nU v n ∈ _
    rw [conj_scalarU]
    exact Subgroup.mem_sup_right ⟨c, rfl⟩

theorem mem_level_meetOrder_of
    (hφ1 : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hφR : ∀ x : CosetGraph.Loc a b v, x ∈ Submodule.localBox R v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ)
    (hSv : ∀ x : CosetGraph.Loc a b v, x ∈ Submodule.localBox (meetOrder R n) v ↔
      x ∈ Submodule.localBox R v ∧
        (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) * x * (nU v n : (CosetGraph.Loc a b v)ˣ) ∈
          Submodule.localBox R v)
    {k : (CosetGraph.Loc a b v)ˣ} (hk : k ∈ scalGL v φ) (hk' : (nU v n)⁻¹ * k * nU v n ∈ scalGL v φ) :
    k ∈ CosetGraph.level (meetOrder R n) v := by
  obtain ⟨c, hc, hG, hGi⟩ := hk
  obtain ⟨c', hc', hG', hGi'⟩ := hk'
  obtain ⟨N, hN⟩ : ∃ N, N = φ ((nU v n : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) := ⟨_, rfl⟩
  obtain ⟨Ni, hNi⟩ : ∃ Ni, Ni = φ (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = φ ((k : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) := ⟨_, rfl⟩
  obtain ⟨Ki, hKi⟩ : ∃ Ki, Ki = φ (((k⁻¹ : (CosetGraph.Loc a b v)ˣ)) : CosetGraph.Loc a b v) := ⟨_, rfl⟩
  have hNN : Ni * N = 1 := by rw [hNi, hN, ← map_mul, Units.inv_mul, map_one]
  have hKK : K * Ki = 1 := by rw [hK, hKi, ← map_mul, Units.mul_inv, map_one]
  have eG' : φ (((nU v n)⁻¹ * k * nU v n : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) = Ni * K * N := by
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hNi, hK, hN]
  have eGi' : φ ((((nU v n)⁻¹ * k * nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) = Ni * Ki * N := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul, map_mul, map_mul, hNi, hKi, hN]
  rw [← hK] at hG; rw [← hKi] at hGi; rw [eG'] at hG'; rw [eGi'] at hGi'

  have dNN : Ni.det * N.det = 1 := by rw [← Matrix.det_mul, hNN, Matrix.det_one]
  have dKK : K.det * Ki.det = 1 := by rw [← Matrix.det_mul, hKK, Matrix.det_one]
  have he0 : c * c'⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero hc')
  have hsq : (c * c'⁻¹) ^ 2 = (c'⁻¹ • (Ni * K * N)).det * (c • Ki).det := by
    rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_mul]
    calc (c * c'⁻¹) ^ 2 = c'⁻¹ ^ 2 * c ^ 2 * (Ni.det * N.det) * (K.det * Ki.det) := by rw [dNN, dKK]; ring
      _ = _ := by ring
  have hsq' : ((c * c'⁻¹) ^ 2)⁻¹ = (c⁻¹ • K).det * (c' • (Ni * Ki * N)).det := by
    rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_mul]
    calc ((c * c'⁻¹) ^ 2)⁻¹ = c⁻¹ ^ 2 * c' ^ 2 * (Ni.det * N.det) * (K.det * Ki.det) := by
          rw [dNN, dKK]; field_simp
      _ = _ := by ring
  have h1 : (c * c'⁻¹) ^ 2 ∈ v.adicCompletionIntegers ℚ := by rw [hsq]; exact mul_mem hG'.det hGi.det
  have h2 : ((c * c'⁻¹) ^ 2)⁻¹ ∈ v.adicCompletionIntegers ℚ := by rw [hsq']; exact mul_mem hG.det hGi'.det
  obtain ⟨heO, heiO⟩ := mem_and_inv_mem_of_sq v he0 h1 h2
  have hu : (scalarU v (Units.mk0 c hc))⁻¹ * k ∈ Submodule.localBoxUnits (meetOrder R n) v := by
    refine ⟨(hSv _).mpr ⟨(hφR _).mpr ?_, (hφR _).mpr ?_⟩, (hSv _).mpr ⟨(hφR _).mpr ?_, (hφR _).mpr ?_⟩⟩
    · rw [Units.val_mul, map_mul, val_scalarU_inv, hφ1, smul_one_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ← hK]
      exact hG
    · rw [Units.val_mul, map_mul, map_mul, map_mul, val_scalarU_inv, hφ1, smul_one_mul, Units.val_inv_eq_inv_val,
        Units.val_mk0, ← hK, ← hN, ← hNi, Matrix.mul_smul, Matrix.smul_mul]
      have e1 : c⁻¹ • (Ni * K * N) = (c * c'⁻¹)⁻¹ • (c'⁻¹ • (Ni * K * N)) := by
        rw [smul_smul, mul_inv, inv_inv, mul_inv_cancel_right₀ hc']
      rw [e1]; exact hG'.smul heiO
    · rw [mul_inv_rev, inv_inv, Units.val_mul, map_mul, val_scalarU, hφ1, mul_smul_one, Units.val_mk0, ← hKi]
      exact hGi
    · rw [mul_inv_rev, inv_inv, Units.val_mul, map_mul, map_mul, map_mul, val_scalarU, hφ1, mul_smul_one, Units.val_mk0,
        ← hKi, ← hN, ← hNi, Matrix.mul_smul, Matrix.smul_mul]
      have e1 : c • (Ni * Ki * N) = (c * c'⁻¹) • (c' • (Ni * Ki * N)) := by
        rw [smul_smul, inv_mul_cancel_right₀ hc']
      rw [e1]; exact hGi'.smul heO
  exact mem_level_of_localBoxUnits v (Units.mk0 c hc) hu

end Clauses

end LocalAL

end

open LocalAL in
theorem solution
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {N : ℕ} [NeZero N] {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsEichlerOrder R N)
    {r : ℕ} [Fact r.Prime] (hrq' : r ≠ q') (hrN : ¬ r ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    {n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hn : n ∈ primeHeckeSet R r)
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n) :
    (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n *
        Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n ∈ CosetGraph.level R v) ∧
    (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n ∉ CosetGraph.level R v) ∧
    (∀ k : (CosetGraph.Loc a b v)ˣ,
      (k ∈ CosetGraph.level R v ∧
        (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n)⁻¹ * k *
          Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n ∈ CosetGraph.level R v) ↔
      k ∈ CosetGraph.level (meetOrder R n) v) := by
  have hr : r.Prime := Fact.out
  have hr0 : r ≠ 0 := hr.ne_zero
  have hRo : IsOrder R := hR.isOrder
  have hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal :=
    natCast_not_mem_asIdeal_of_coprime ((Nat.coprime_primes hr Fact.out).mpr hrq') v hv
  have hNv : (N : 𝓞 ℚ) ∉ v.asIdeal :=
    natCast_not_mem_asIdeal_of_coprime ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrN) v hv
  obtain ⟨-, φ, hφ1, hφR, k₀, k₀i, hk₀, hk₀i, h1, h2, hn1, hn2⟩ :=
    QuaternionAlgebra.exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet
      hdef hR r hr v hv hq'v hNv n hn
  have hn1' : φ ((nU v n : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) =
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((r : ℕ) : v.adicCompletion ℚ)] * k₀ := by
    rw [← D_eq]; exact hn1
  have hn2' : φ (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) =
      k₀i * Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((r : ℕ) : v.adicCompletion ℚ)⁻¹] := by
    rw [← D_eq]; exact hn2
  have hp0 : ((r : ℕ) : v.adicCompletion ℚ) ≠ 0 := natCast_ne_zero_adicCompletion hr0 v
  have hSv := mem_localBox_meetOrder_iff hRo n v
  have hconj : ∀ y ∈ Submodule.localBox (meetOrder R n) v,
      (nU v n : (CosetGraph.Loc a b v)ˣ) * y * (((nU v n)⁻¹ : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Loc a b v) ∈
        Submodule.localBox R v :=
    fun y hy => conj_mem_localBox_of_conjByFiniteIdele_eq hRo n hnorm v hy
  obtain ⟨hs, hz⟩ := key_entries hp0 hφR hSv hconj hk₀ hk₀i h1 hn1' hn2'
  obtain ⟨hi1, hi2⟩ := isInt_sq hp0 hk₀ hk₀i hs hz hn1' hn2'
  refine ⟨mem_level_of_isInt hφ1 hφR hp0 hi1 hi2, ?_, ?_⟩
  · exact fun h => not_mem_scalGL hr0 hv hk₀ hk₀i h1 hn1' hn2' (level_le_scalGL hφ1 hφR h)
  · intro k
    refine ⟨fun hk => ?_, fun hk => mem_and_conj_mem_of_mem_level_meetOrder hRo n v hk⟩
    exact mem_level_meetOrder_of hφ1 hφR hSv (level_le_scalGL hφ1 hφR hk.1) (level_le_scalGL hφ1 hφR hk.2)

end S_CerednikDrinfeld_CosetGraph_mul_self_mem_level_and_not_mem_level_and_mem_inf_conj_iff_of_mem_primeHeckeSet
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_mul_self_mem_level_and_not_mem_level_and_mem_inf_conj_iff_of_mem_primeHeckeSet (solution)
