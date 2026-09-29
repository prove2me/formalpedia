-- Prove2me | solution 1 for CuspForm.IsNewform.not_isCuspidalOfType_subrepresentation_gl2ReductionRep_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9f15ac28-a5bc-58c1-bcda-e0917d66942d

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import Theorems.Thm_CuspForm_IsNewform_hasNewvectorConductor_adelicSpan_factorization_of_isAdelicLiftOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_not_isCuspidalOfType_subrepresentation_gl2ReductionRep_of_dvd
p2m_attr_erase "instance" "LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv"

set_option autoImplicit false

noncomputable section

namespace MirabolicConstantVector

section FiniteGroup

variable {q : ℕ} [Fact q.Prime]

private scoped instance neZero_of_fact_prime : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

private theorem unipotent_mul (s t : ZMod q) :
    CuspidalType.unipotent q s * CuspidalType.unipotent q t = CuspidalType.unipotent q (s + t) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, CuspidalType.unipotent_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem unipotent_zero : CuspidalType.unipotent q 0 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [CuspidalType.unipotent_val, Matrix.GeneralLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

private theorem diagElem_mul (a b : (ZMod q)ˣ) :
    CuspidalType.diagElem q a * CuspidalType.diagElem q b = CuspidalType.diagElem q (a * b) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [CuspidalType.diagElem_val, Units.val_mul]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagElem_one : CuspidalType.diagElem q 1 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [CuspidalType.diagElem_val, Matrix.GeneralLinearGroup.coe_one, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp

private theorem diagElem_mul_unipotent (a : (ZMod q)ˣ) (t : ZMod q) :
    CuspidalType.diagElem q a * CuspidalType.unipotent q t =
      CuspidalType.unipotent q ((a : ZMod q) * t) * CuspidalType.diagElem q a := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, CuspidalType.diagElem_val, CuspidalType.unipotent_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem exists_eq_diagElem (r : CuspidalType.GL2 q)
    (h01 : (r : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 = 0) (h10 : (r : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0)
    (h11 : (r : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 = 1) :
    ∃ a : (ZMod q)ˣ, r = CuspidalType.diagElem q a := by
  have hdet : IsUnit ((r : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) := by
    have h := (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit r)
    rwa [Matrix.det_fin_two, h01, h10, h11, mul_one, mul_zero, sub_zero] at h
  refine ⟨hdet.unit, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [CuspidalType.diagElem_val]
  fin_cases i <;> fin_cases j
  · simp [IsUnit.unit_spec]
  · simpa using h01
  · simpa using h10
  · simpa using h11

variable {X : Type*} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (CuspidalType.GL2 q) X)

private def ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar

private theorem ψ_isPrimitive : (ψ : AddChar (ZMod q) ℂ).IsPrimitive := ZMod.isPrimitive_stdAddChar q

private def proj (a : ZMod q) : X →ₗ[ℂ] X :=
  (q : ℂ)⁻¹ • ∑ t : ZMod q, (ψ (-(a * t))) • ρ (CuspidalType.unipotent q t)

private theorem proj_apply (a : ZMod q) (v : X) :
    proj ρ a v = (q : ℂ)⁻¹ • ∑ t : ZMod q, (ψ (-(a * t))) • ρ (CuspidalType.unipotent q t) v := by
  simp [proj, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem q_ne_zero : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : q.Prime).ne_zero

private theorem rep_apply_apply (g h : CuspidalType.GL2 q) (v : X) : ρ g (ρ h v) = ρ (g * h) v := by
  rw [map_mul]
  rfl

private theorem unipotent_proj (a s : ZMod q) (v : X) :
    ρ (CuspidalType.unipotent q s) (proj ρ a v) = ψ (a * s) • proj ρ a v := by
  rw [proj_apply, LinearMap.map_smul, map_sum]
  conv_rhs => rw [smul_comm]
  congr 1
  have hterm : ∀ t : ZMod q, ρ (CuspidalType.unipotent q s) (ψ (-(a * t)) • ρ (CuspidalType.unipotent q t) v)
      = ψ (-(a * t)) • ρ (CuspidalType.unipotent q (s + t)) v := by
    intro t
    rw [LinearMap.map_smul, rep_apply_apply, unipotent_mul]
  simp_rw [hterm]
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft s) _ _ fun t => ?_
  simp only [Equiv.coe_addLeft]
  rw [← mul_smul, ← AddChar.map_add_eq_mul]
  congr 2
  ring

private theorem sum_proj_apply (v : X) : ∑ a : ZMod q, proj ρ a v = v := by
  classical
  simp_rw [proj_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hinner : ∀ t : ZMod q, ∑ a : ZMod q, ψ (-(a * t)) • ρ (CuspidalType.unipotent q t) v
      = (if t = 0 then (q : ℂ) else 0) • ρ (CuspidalType.unipotent q t) v := by
    intro t
    rw [← Finset.sum_smul]
    congr 1
    have h := AddChar.sum_mulShift (-t) (ψ_isPrimitive (q := q))
    simp only [ZMod.card, neg_eq_zero, Nat.cast_ite, Nat.cast_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    ring
  simp_rw [hinner]
  rw [Finset.sum_eq_single (0 : ZMod q)]
  · rw [if_pos rfl, unipotent_zero, map_one, Module.End.one_apply, ← mul_smul,
      inv_mul_cancel₀ q_ne_zero, one_smul]
  · intro t _ ht
    rw [if_neg ht, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem proj_zero_apply
    (hcusp : ∀ v : X, (∀ t : ZMod q, ρ (CuspidalType.unipotent q t) v = v) → v = 0) (v : X) :
    proj ρ 0 v = 0 := by
  apply hcusp
  intro t
  rw [unipotent_proj, zero_mul, AddChar.map_zero_eq_one, one_smul]

private theorem proj_proj_apply (a b : ZMod q) (v : X) :
    proj ρ a (proj ρ b v) = if a = b then proj ρ b v else 0 := by
  classical
  rw [proj_apply ρ a]
  simp_rw [unipotent_proj, ← mul_smul]
  rw [← Finset.sum_smul, ← mul_smul]
  have hsum : ∑ s : ZMod q, ψ (-(a * s)) * ψ (b * s) = if b - a = 0 then (q : ℂ) else 0 := by
    have h := AddChar.sum_mulShift (b - a) (ψ_isPrimitive (q := q))
    simp only [ZMod.card, Nat.cast_ite, Nat.cast_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hsum]
  by_cases hab : a = b
  · subst hab
    rw [sub_self, if_pos rfl, if_pos rfl, inv_mul_cancel₀ q_ne_zero, one_smul]
  · rw [if_neg (show ¬ (b - a = 0) from fun h => hab (sub_eq_zero.1 h).symm), if_neg hab, mul_zero, zero_smul]

private theorem diagElem_proj_apply (c : (ZMod q)ˣ) (a : ZMod q) (v : X) :
    ρ (CuspidalType.diagElem q c) (proj ρ a v) =
      proj ρ (a * ((c⁻¹ : (ZMod q)ˣ) : ZMod q)) (ρ (CuspidalType.diagElem q c) v) := by
  rw [proj_apply, proj_apply, LinearMap.map_smul, map_sum]
  congr 1
  have hterm : ∀ t : ZMod q,
      ρ (CuspidalType.diagElem q c) (ψ (-(a * t)) • ρ (CuspidalType.unipotent q t) v)
        = ψ (-(a * t)) • ρ (CuspidalType.unipotent q ((c : ZMod q) * t)) (ρ (CuspidalType.diagElem q c) v) := by
    intro t
    rw [LinearMap.map_smul, rep_apply_apply, diagElem_mul_unipotent, ← rep_apply_apply]
  simp_rw [hterm]
  refine Fintype.sum_equiv (c.mulLeft) _ _ fun t => ?_
  simp only [Units.mulLeft_apply]
  rw [mul_assoc, Units.inv_mul_cancel_left]

private theorem exists_ne_zero_forall_diagElem_apply_eq (hX : ∃ v : X, v ≠ 0)
    (hcusp : ∀ v : X, (∀ t : ZMod q, ρ (CuspidalType.unipotent q t) v = v) → v = 0) :
    ∃ w : X, w ≠ 0 ∧ ∀ c : (ZMod q)ˣ, ρ (CuspidalType.diagElem q c) w = w := by
  classical
  obtain ⟨v, hv⟩ := hX
  obtain ⟨a₀, -, ha₀⟩ : ∃ a₀ ∈ (Finset.univ : Finset (ZMod q)), proj ρ a₀ v ≠ 0 := by
    apply Finset.exists_ne_zero_of_sum_ne_zero
    rw [sum_proj_apply]
    exact hv
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    exact ha₀ (proj_zero_apply ρ hcusp v)
  set w₀ := proj ρ a₀ v with hw₀
  have hterm : ∀ c : (ZMod q)ˣ,
      proj ρ a₀ (ρ (CuspidalType.diagElem q c) w₀) = if c = 1 then w₀ else 0 := by
    intro c
    have h1 : proj ρ a₀ (ρ (CuspidalType.diagElem q c) w₀)
        = ρ (CuspidalType.diagElem q c) (proj ρ (a₀ * (c : ZMod q)) w₀) := by
      conv_rhs => rw [diagElem_proj_apply, Units.mul_inv_cancel_right]
    rw [h1, hw₀, proj_proj_apply]
    by_cases hc : c = 1
    · subst hc
      rw [if_pos (show a₀ * ((1 : (ZMod q)ˣ) : ZMod q) = a₀ by rw [Units.val_one, mul_one]), if_pos rfl,
        diagElem_one, map_one, Module.End.one_apply]
    · have hne : a₀ * (c : ZMod q) ≠ a₀ := by
        rwa [Ne, mul_eq_left₀ ha₀0, Units.val_eq_one]
      rw [if_neg hne, if_neg hc, map_zero]
  refine ⟨∑ c : (ZMod q)ˣ, ρ (CuspidalType.diagElem q c) w₀, ?_, ?_⟩
  · intro hzero
    have key : proj ρ a₀ (∑ c : (ZMod q)ˣ, ρ (CuspidalType.diagElem q c) w₀) = w₀ := by
      rw [map_sum]
      simp_rw [hterm]
      rw [Finset.sum_ite_eq' Finset.univ (1 : (ZMod q)ˣ) (fun _ => w₀), if_pos (Finset.mem_univ _)]
    rw [hzero, map_zero] at key
    exact ha₀ key.symm
  · intro b
    rw [map_sum]
    have hmul : ∀ c : (ZMod q)ˣ, ρ (CuspidalType.diagElem q b) (ρ (CuspidalType.diagElem q c) w₀)
        = ρ (CuspidalType.diagElem q (b * c)) w₀ := by
      intro c
      rw [rep_apply_apply, diagElem_mul]
    simp_rw [hmul]
    exact Fintype.sum_equiv (Equiv.mulLeft b) _ _ fun c => rfl

private theorem apply_eq_of_forall_diagElem {w : X} (hw : ∀ c : (ZMod q)ˣ, ρ (CuspidalType.diagElem q c) w = w)
    (r : CuspidalType.GL2 q) (h01 : (r : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 = 0)
    (h10 : (r : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0) (h11 : (r : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 = 1) :
    ρ r w = w := by
  obtain ⟨a, rfl⟩ := exists_eq_diagElem r h01 h10 h11
  exact hw a

end FiniteGroup

section Padic

variable (q : ℕ) [Fact q.Prime]

private def diagGL (c : ℚ_[q]) (hc : c ≠ 0) : GL (Fin 2) ℚ_[q] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![c, 1])
    (by rw [Matrix.det_diagonal, Fin.prod_univ_two]; simpa using hc)

private theorem diagGL_val (c : ℚ_[q]) (hc : c ≠ 0) :
    (diagGL q c hc : Matrix (Fin 2) (Fin 2) ℚ_[q]) = Matrix.diagonal ![c, 1] :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private theorem diagGL_mul (c c' : ℚ_[q]) (hc : c ≠ 0) (hc' : c' ≠ 0) :
    diagGL q c hc * diagGL q c' hc' = diagGL q (c * c') (mul_ne_zero hc hc') := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, diagGL_val, Matrix.diagonal_mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp

private theorem diagGL_one : diagGL q 1 one_ne_zero = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [diagGL_val, Matrix.GeneralLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

private theorem natCast_ne_zero : ((q : ℕ) : ℚ_[q]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : q.Prime).ne_zero

private def tElem : GL (Fin 2) ℚ_[q] := diagGL q (q : ℚ_[q]) (natCast_ne_zero q)

private def tInv : GL (Fin 2) ℚ_[q] := diagGL q ((q : ℚ_[q])⁻¹) (inv_ne_zero (natCast_ne_zero q))

private theorem tElem_mul_tInv : tElem q * tInv q = 1 := by
  rw [tElem, tInv, diagGL_mul]
  convert diagGL_one q using 2
  exact mul_inv_cancel₀ (natCast_ne_zero q)

private theorem tInv_mul_tElem : tInv q * tElem q = 1 := by
  rw [tElem, tInv, diagGL_mul]
  convert diagGL_one q using 2
  exact inv_mul_cancel₀ (natCast_ne_zero q)

private theorem map_mem_gl2CongruenceSubgroup_zero (y : GL (Fin 2) ℤ_[q]) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) y ∈
      FLT.SmoothVectors.gl2CongruenceSubgroup q 0 := by
  rw [LocalNewvector.mem_gl2CongruenceSubgroup_zero_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one _
  · rw [← map_inv, Matrix.GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one _

private theorem conj_padicK1_two {k : GL (Fin 2) ℚ_[q]} (hk : k ∈ LocalNewvector.padicK1 q 2) :
    ∃ hk0 : tElem q * k * tInv q ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 0,
      ((LocalNewvector.gl2ReductionHom q ⟨_, hk0⟩ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 = 0 ∧
      ((LocalNewvector.gl2ReductionHom q ⟨_, hk0⟩ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 ∧
      ((LocalNewvector.gl2ReductionHom q ⟨_, hk0⟩ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1
        = 1 := by
  obtain ⟨y, hy, hc, hd⟩ := LocalNewvector.mem_congruenceK1_iff.1 hk
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 hc
  obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton'.1 hd

  set A : Matrix (Fin 2) (Fin 2) ℤ_[q] :=
    !![(y : Matrix (Fin 2) (Fin 2) ℤ_[q]) 0 0, (q : ℤ_[q]) * (y : Matrix (Fin 2) (Fin 2) ℤ_[q]) 0 1;
       (q : ℤ_[q]) * c', (y : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1] with hA
  have hdetA : A.det = (y : Matrix (Fin 2) (Fin 2) ℤ_[q]).det := by
    rw [hA, Matrix.det_fin_two_of, Matrix.det_fin_two, ← hc']
    ring
  have hAunit : IsUnit A.det := by
    rw [hdetA]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit y)
  have hmap : Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q])
      (Matrix.GeneralLinearGroup.mk'' A hAunit) = tElem q * k * tInv q := by
    rw [← hy]
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have hq0 := natCast_ne_zero q
    have h10 :
        (((y : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 : ℤ_[q]) : ℚ_[q]) = (q : ℚ_[q]) * (c' : ℚ_[q]) * (q : ℚ_[q]) := by
      rw [← hc', PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
      ring
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.val_mk'', PadicInt.algebraMap_apply,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, tElem, tInv, diagGL_val, diagGL_val,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply, hA]
    fin_cases i <;> fin_cases j
    · show (((y : Matrix (Fin 2) (Fin 2) ℤ_[q]) 0 0 : ℤ_[q]) : ℚ_[q])
        = (q : ℚ_[q]) * (((y : Matrix (Fin 2) (Fin 2) ℤ_[q]) 0 0 : ℤ_[q]) : ℚ_[q]) * (q : ℚ_[q])⁻¹
      rw [mul_comm (q : ℚ_[q]) _, mul_inv_cancel_right₀ hq0]
    · show ((((q : ℤ_[q]) * (y : Matrix (Fin 2) (Fin 2) ℤ_[q]) 0 1 : ℤ_[q])) : ℚ_[q])
        = (q : ℚ_[q]) * (((y : Matrix (Fin 2) (Fin 2) ℤ_[q]) 0 1 : ℤ_[q]) : ℚ_[q]) * 1
      rw [mul_one, PadicInt.coe_mul, PadicInt.coe_natCast]
    · show ((((q : ℤ_[q]) * c' : ℤ_[q])) : ℚ_[q])
        = 1 * (((y : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 : ℤ_[q]) : ℚ_[q]) * (q : ℚ_[q])⁻¹
      rw [one_mul, h10, mul_inv_cancel_right₀ hq0, PadicInt.coe_mul, PadicInt.coe_natCast]
    · show (((y : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1 : ℤ_[q]) : ℚ_[q])
        = 1 * (((y : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1 : ℤ_[q]) : ℚ_[q]) * 1
      rw [one_mul, mul_one]
  have hk0 : tElem q * k * tInv q ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 0 := by
    rw [← hmap]
    exact map_mem_gl2CongruenceSubgroup_zero q _
  have hentry : ∀ i j : Fin 2,
      ((A i j : ℤ_[q]) : ℚ_[q]) = ((tElem q * k * tInv q : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j := by
    intro i j
    rw [← hmap, Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.val_mk'', PadicInt.algebraMap_apply]
  have hy11 : (y : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1 = 1 + d' * (q : ℤ_[q]) ^ 2 := by
    rw [hd']
    ring
  refine ⟨hk0, ?_, ?_, ?_⟩
  · rw [LocalNewvector.gl2ReductionHom_apply_of_coe_eq q ⟨_, hk0⟩ 0 1 (A 0 1) (hentry 0 1), hA]
    simp [map_mul, map_natCast]
  · rw [LocalNewvector.gl2ReductionHom_apply_of_coe_eq q ⟨_, hk0⟩ 1 0 (A 1 0) (hentry 1 0), hA]
    simp [map_mul, map_natCast]
  · rw [LocalNewvector.gl2ReductionHom_apply_of_coe_eq q ⟨_, hk0⟩ 1 1 (A 1 1) (hentry 1 1), hA]
    simp [hy11, map_add, map_mul, map_pow, map_natCast]

end Padic

section SpanZero

private theorem adelicSpan_zero_eq_zero
    (z : LocalNewvector.AdelicSpan (0 : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)) :
    z = 0 := by
  apply LocalNewvector.AdelicSpan.ext
  have hz := (z : LocalNewvector.AdelicSpanSubmodule
    (0 : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)).2
  have hle : LocalNewvector.AdelicSpanSubmodule
      (0 : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) ≤ ⊥ := by
    rw [LocalNewvector.AdelicSpanSubmodule, Submodule.span_le]
    rintro ψ ⟨g, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_bot]
    apply LocalNewvector.AdelicFnCarrier.ext
    intro x
    rfl
  exact (Submodule.mem_bot ℂ).1 (hle hz)

end SpanZero

end MirabolicConstantVector
p2m_reactivate "P2MW.S_CuspForm_IsNewform_not_isCuspidalOfType_subrepresentation_gl2ReductionRep_of_dvd.MirabolicConstantVector"

open MirabolicConstantVector in
theorem solution
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M']
    {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2} (hg : g.IsNewform) (hqM' : q ∣ M')
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ
      ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v) (hfinj : Function.Injective f)
    (θ : (GaloisField q 2)ˣ →* ℂˣ)
    (W : Subrepresentation (LocalNewvector.gl2ReductionRep q V)) :
    ¬ CuspidalType.IsCuspidalOfType θ W.toRepresentation := by
  intro hW
  classical
  have hq := (Fact.out : q.Prime)
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero 2 hq.ne_zero) (NeZero.ne M')⟩

  have hX : ∃ v : ↥W.toSubmodule, v ≠ 0 := by
    have hpos : 0 < Module.finrank ℂ ↥W.toSubmodule := by
      rw [hW.finrank_eq]
      have := hq.two_le
      omega
    haveI := Module.nontrivial_of_finrank_pos hpos
    exact exists_ne 0
  obtain ⟨w, hw0, hwfix⟩ := exists_ne_zero_forall_diagElem_apply_eq W.toRepresentation hX hW.cuspidal

  set y : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) :=
    (w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)) with hy
  set x₀ : V := (y : V) with hx₀
  have hx₀0 : x₀ ≠ 0 := by
    intro h
    apply hw0
    apply Subtype.ext
    apply Subtype.ext
    simpa [hx₀, hy] using h
  have hyfix : ∀ r : CuspidalType.GL2 q, (r : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 = 0 →
      (r : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 → (r : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 = 1 →
      LocalNewvector.gl2ReductionRep q V r y = y := by
    intro r h01 h10 h11
    have h := apply_eq_of_forall_diagElem W.toRepresentation hwfix r h01 h10 h11
    have h' := congrArg Subtype.val h
    exact h'

  have hK0fix : ∀ (k : GL (Fin 2) ℚ_[q]) (hk : k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 0),
      ((LocalNewvector.gl2ReductionHom q ⟨k, hk⟩ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 = 0 →
      ((LocalNewvector.gl2ReductionHom q ⟨k, hk⟩ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 →
      ((LocalNewvector.gl2ReductionHom q ⟨k, hk⟩ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 = 1 →
      k • x₀ = x₀ := by
    intro k hk h01 h10 h11
    have h := LocalNewvector.gl2ReductionRep_gl2ReductionHom_apply q V ⟨k, hk⟩ y
    rw [hyfix _ h01 h10 h11] at h
    exact h.symm

  set x₁ : V := tInv q • x₀ with hx₁
  have hx₁fix : ∀ k ∈ LocalNewvector.padicK1 q 2, k • x₁ = x₁ := by
    intro k hk
    obtain ⟨hk0, h01, h10, h11⟩ := conj_padicK1_two q hk
    have hfix := hK0fix _ hk0 h01 h10 h11
    calc k • x₁ = (tInv q * (tElem q * k * tInv q)) • x₀ := by
          rw [hx₁, ← mul_smul, ← mul_assoc, ← mul_assoc, tInv_mul_tElem, one_mul]
      _ = x₁ := by rw [mul_smul, hfix]

  set z : LocalNewvector.AdelicSpan Φ := f x₁ with hz
  have hzfix : z ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q 2) (LocalNewvector.AdelicSpan Φ) := by
    rw [LocalNewvector.mem_fixedSubmodule_iff]
    intro k hk
    rw [hz, ← hf, hx₁fix k hk]
  have hz0 : z ≠ 0 := by
    intro h
    apply hx₀0
    have hx₁0 : x₁ = 0 := hfinj (by rw [← hz, h, map_zero])
    calc x₀ = (tElem q * tInv q) • x₀ := by rw [tElem_mul_tInv, one_smul]
      _ = 0 := by rw [mul_smul, ← hx₁, hx₁0, smul_zero]

  by_cases hΦ0 : Φ = 0
  · subst hΦ0
    exact hz0 (adelicSpan_zero_eq_zero z)
  have hcond := hg.hasNewvectorConductor_adelicSpan_factorization_of_isAdelicLiftOf Φ hΦ0 hΦg q
  have hlt : 2 < (q ^ 2 * M').factorization q := by
    have hM' : M' ≠ 0 := NeZero.ne M'
    rw [Nat.factorization_mul (pow_ne_zero 2 hq.ne_zero) hM', Finsupp.add_apply, Nat.factorization_pow,
      Finsupp.smul_apply, hq.factorization_self, smul_eq_mul, mul_one]
    have h1 : 1 ≤ M'.factorization q := (hq.dvd_iff_one_le_factorization hM').1 hqM'
    omega
  have hbot : LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q 2) (LocalNewvector.AdelicSpan Φ) = ⊥ :=
    (show _ ∧ _ from hcond).2 2 hlt
  rw [hbot, Submodule.mem_bot] at hzfix
  exact hz0 hzfix

end
p2m_reactivate "P2MW.S_CuspForm_IsNewform_not_isCuspidalOfType_subrepresentation_gl2ReductionRep_of_dvd.MirabolicConstantVector"

end S_CuspForm_IsNewform_not_isCuspidalOfType_subrepresentation_gl2ReductionRep_of_dvd
end P2MW
export P2MW.S_CuspForm_IsNewform_not_isCuspidalOfType_subrepresentation_gl2ReductionRep_of_dvd (solution)
