-- Prove2me | solution 1 for CuspForm.qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6ada2d87-add8-5bdc-8c67-13313f2cb9c7

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import Theorems.Thm_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
import Theorems.Thm_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0
import Theorems.Thm_ModularFormClass_qExpansion_heckeU_eq_heckeU
import Theorems.Thm_ModularForm_exists_coe_eq_slash_of_mem_gamma0_gammaH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace UTRatIhl

open UpperHalfPlane

theorem algRat_eq : (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ)) = AlgebraicClosure.instAlgebra ℚ :=
  Subsingleton.elim _ _

scoped instance instIsAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  have : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
  rwa [← algRat_eq] at this

scoped instance instNormalQbar : Normal ℚ (AlgebraicClosure ℚ) := by
  have : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
  rwa [← algRat_eq] at this

scoped instance instIsGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  haveI : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  ⟨⟩

theorem mem_range_algebraMap_of_forall_algEquiv (x : AlgebraicClosure ℚ)
    (hx : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ x = x) :
    x ∈ (algebraMap ℚ (AlgebraicClosure ℚ)).range := by
  have hmem : x ∈ IntermediateField.fixedField (⊤ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    fun σ => hx σ
  rw [InfiniteGalois.fixedField_bot] at hmem
  exact IntermediateField.mem_bot.mp hmem

theorem exists_coprime_forall_pow_eq_one_apply_eq_pow (M : ℕ) [NeZero M]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ c : ℕ, c.Coprime M ∧ ∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c := by
  haveI : HasEnoughRootsOfUnity (AlgebraicClosure ℚ) M := IsSepClosed.hasEnoughRootsOfUnity _ M
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) M
  have hσζ : (σ ζ₀) ^ M = 1 := by rw [← map_pow, hζ₀.pow_eq_one, map_one]
  obtain ⟨c, -, hc⟩ := hζ₀.eq_pow_of_pow_eq_one hσζ
  refine ⟨c, ?_, ?_⟩
  · have hprim : IsPrimitiveRoot (σ ζ₀) M := hζ₀.map_of_injective σ.injective
    rw [← hc] at hprim
    exact (hζ₀.pow_iff_coprime (NeZero.pos M) c).mp hprim
  · intro ζ hζ
    obtain ⟨i, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
    rw [map_pow, ← hc, ← pow_mul, ← pow_mul, mul_comm]

theorem exists_mem_Gamma0_apply_eq (M : ℕ) [NeZero M] {c : ℕ} (hc : c.Coprime M) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M ∧ ((γ 1 1 : ℤ) : ZMod M) = c := by
  let u : (ZMod M)ˣ := ZMod.unitOfCoprime c hc
  refine ⟨(CuspForm.gammaLift M u : CongruenceSubgroup.Gamma0 M), (CuspForm.gammaLift M u).2, ?_⟩
  have h := congrArg (fun v : (ZMod M)ˣ => (v : ZMod M)) (CuspForm.gamma0Units_gammaLift (M := M) u)
  simp [u, CohCarrier.val_gamma0Units] at h
  exact h

section QExp
variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ} {ι : Type*}

theorem coe_sum_smul (s : Finset ι) (c : ι → ℂ) (X : ι → ModularForm Γ k) :
    (⇑(∑ j ∈ s, c j • X j) : ℍ → ℂ) = ∑ j ∈ s, c j • (⇑(X j) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ModularForm.IsGLPos.coe_smul, ih]

theorem qExpansion_coe_sum_smul (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (s : Finset ι) (c : ι → ℂ) (X : ι → ModularForm Γ k) :
    qExpansion 1 (⇑(∑ j ∈ s, c j • X j) : ℍ → ℂ) = ∑ j ∈ s, c j • qExpansion 1 (⇑(X j) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add,
        ModularForm.qExpansion_add one_pos hΓ (c a • X a) (∑ j ∈ s, c j • X j), ih,
        ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos hΓ (c a) (X a)]

omit [Γ.HasDetOne] in
theorem eq_of_qExpansion_eq (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f g : ModularForm Γ k)
    (h : qExpansion 1 (⇑f : ℍ → ℂ) = qExpansion 1 (⇑g : ℍ → ℂ)) : f = g := by
  have h0 : qExpansion 1 (⇑(f - g) : ℍ → ℂ) = 0 := by
    rw [ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos hΓ f g, h, sub_self]
  exact sub_eq_zero.mp ((ModularForm.qExpansion_eq_zero_iff one_pos hΓ (f - g)).mp h0)

end QExp

theorem one_mem_strictPeriods_Gamma1 (M : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

end UTRatIhl
p2m_reactivate "P2MW.S_CuspForm_qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range.UTRatIhl"

namespace TTU

theorem sum_slash {ι : Type*} (s : Finset ι) (k : ℤ) (F : ι → UpperHalfPlane → ℂ) (A : GL (Fin 2) ℝ) :
    (∑ i ∈ s, F i) ∣[k] A = ∑ i ∈ s, F i ∣[k] A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

noncomputable def upperMat (r : ℕ) (hr : r ≠ 0) (x : ℤ) : GL (Fin 2) ℝ :=
  ModularForm.upperTriangularGL 1 x r (by rw [one_mul]; exact_mod_cast hr)

@[scoped simp] theorem val_upperMat (r : ℕ) (hr : r ≠ 0) (x : ℤ) :
    ((upperMat r hr x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (x : ℝ); 0, (r : ℝ)] := by
  simp [upperMat]

theorem upperMat_natCast (r : ℕ) (hr : r ≠ 0) (j : ℕ) :
    upperMat r hr (j : ℤ) = ModularForm.heckeMatrix r j := by
  apply Units.ext
  rw [val_upperMat, ModularForm.val_heckeMatrix hr]
  simp

theorem mapGL_T_mul_upperMat (r : ℕ) (hr : r ≠ 0) (x : ℤ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) * upperMat r hr x = upperMat r hr (x + r) := by
  apply Units.ext
  rw [Units.val_mul, val_upperMat, val_upperMat, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, ModularGroup.coe_T]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_transpose_T_pow (n : ℕ) :
    ((Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ n) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(1 : ℤ), 0; (n : ℤ), 1] := by
  rw [Matrix.SpecialLinearGroup.coe_transpose, ← zpow_natCast, ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem heckeDiag_mul_transpose_mul_fricke (M : ℕ) (r : ℕ) (hr : r ≠ 0) (j : ℕ)
    (W : GL (Fin 2) ℝ) (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ModularForm.heckeDiagMatrix r *
        (Matrix.SpecialLinearGroup.mapGL ℝ (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) :
          GL (Fin 2) ℝ) * W =
      W * upperMat r hr (-(j : ℤ)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hW, val_upperMat, ModularForm.val_heckeDiagMatrix hr,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    coe_transpose_T_pow]
  ext i j'
  fin_cases i <;> fin_cases j' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.vecMul, dotProduct]

theorem slash_fricke_slash_T_zpow (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (W : GL (Fin 2) ℝ) (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0])
    (φ : UpperHalfPlane → ℂ)
    (hφ : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), φ ∣[k] γ = φ) (m : ℤ) :
    (φ ∣[k] W) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ m) : GL (Fin 2) ℝ) = φ ∣[k] W := by

  let L : SL(2, ℤ) := ⟨!![1, 0; -((M : ℤ) * m), 1], by simp [Matrix.det_fin_two_of]⟩
  have hL1 : L ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩ <;> simp [L]
  have hL0 : L ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [L]
  have hLH' : L ∈ CohCarrier.GammaH M H := by
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨hL0, ?_⟩
    have : CohCarrier.gamma0Units M ⟨L, hL0⟩ = 1 := by
      ext; simp [CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map, L]
    rw [this]; exact one_mem H
  have hLH : (Matrix.SpecialLinearGroup.mapGL ℝ L : GL (Fin 2) ℝ) ∈
      (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.mem_map_of_mem _ hLH'

  have hmat : (Matrix.SpecialLinearGroup.mapGL ℝ L : GL (Fin 2) ℝ) * W =
      W * (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ m) : GL (Fin 2) ℝ) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hW, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, ModularGroup.coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [L, Matrix.mul_apply, Fin.sum_univ_two]
  rw [← SlashAction.slash_mul, ← hmat, SlashAction.slash_mul, hφ _ hLH]

theorem sum_slash_transpose_slash_fricke_eq_heckeU_slash_fricke
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (r : ℕ) (hr : r ≠ 0) (k : ℤ)
    (W : GL (Fin 2) ℝ) (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0])
    (φ : UpperHalfPlane → ℂ)
    (hφ : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), φ ∣[k] γ = φ) :
    (∑ j ∈ Finset.range r,
        φ ∣[k] (ModularForm.heckeDiagMatrix r *
          (Matrix.SpecialLinearGroup.mapGL ℝ
            (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ))) ∣[k] W =
      ModularForm.heckeU k r (φ ∣[k] W) := by
  set ψ := φ ∣[k] W with hψ

  have hterm : ∀ j : ℕ, (φ ∣[k] (ModularForm.heckeDiagMatrix r *
          (Matrix.SpecialLinearGroup.mapGL ℝ
            (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ))) ∣[k] W =
        ψ ∣[k] upperMat r hr ((r : ℤ) - j) := by
    intro j
    rw [← SlashAction.slash_mul, heckeDiag_mul_transpose_mul_fricke M r hr j W hW, SlashAction.slash_mul,
      show ((r : ℤ) - j) = -(j : ℤ) + r by ring, ← mapGL_T_mul_upperMat, SlashAction.slash_mul]
    congr 1
    have := slash_fricke_slash_T_zpow M H k W hW φ hφ 1
    rw [zpow_one] at this
    first | exact this | exact this.symm
  rw [sum_slash, Finset.sum_congr rfl fun j _ => hterm j, ModularForm.heckeU_def]

  set a : ℕ → (UpperHalfPlane → ℂ) := fun i => ψ ∣[k] upperMat r hr (i : ℤ) with ha
  have hcast : ∀ j ∈ Finset.range r, ψ ∣[k] upperMat r hr ((r : ℤ) - j) = a (r - j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [ha]
    rw [Nat.cast_sub hj.le]
  rw [Finset.sum_congr rfl hcast]
  have har : a r = a 0 := by
    simp only [ha]
    rw [show ((r : ℕ) : ℤ) = 0 + r by ring, ← mapGL_T_mul_upperMat, SlashAction.slash_mul]
    congr 1
    have := slash_fricke_slash_T_zpow M H k W hW φ hφ 1
    rw [zpow_one] at this
    first | exact this | exact this.symm
  have hrefl : ∑ j ∈ Finset.range r, a (r - j) = ∑ i ∈ Finset.range r, a (i + 1) := by
    rw [← Finset.sum_range_reflect (fun i => a (i + 1)) r]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    congr 1
    omega
  rw [hrefl]
  have hshift : ∑ i ∈ Finset.range r, a (i + 1) = ∑ i ∈ Finset.range r, a i := by
    have h1 := Finset.sum_range_succ a r
    have h2 := Finset.sum_range_succ' a r
    rw [har] at h1
    have := h2.symm.trans h1
    exact add_right_cancel this
  rw [hshift]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ha]
  rw [upperMat_natCast]

theorem slash_scalar (k : ℤ) (u : ℝˣ) (φ : UpperHalfPlane → ℂ) :
    φ ∣[k] (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = (((u : ℝ) : ℂ) ^ (k - 2)) • φ := by
  funext τ
  rw [ModularForm.slash_apply, UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar, Pi.smul_apply,
    smul_eq_mul]
  have hdet : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u).det : ℝ) = u * u := by
    rw [Matrix.GeneralLinearGroup.det_scalar]; simp [pow_two]
  have hu0 : (u : ℝ) ≠ 0 := u.ne_zero
  have hpos : 0 < ((Matrix.GeneralLinearGroup.scalar (Fin 2) u).det : ℝ) := by
    rw [hdet]; exact mul_self_pos.mpr hu0
  have hσ : ∀ z : ℂ, (UpperHalfPlane.σ (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) z = z := fun z => by
    rw [UpperHalfPlane.σ, if_pos hpos]; rfl
  rw [hσ, hdet, abs_of_pos (mul_self_pos.mpr hu0)]
  have huC : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu0
  rw [Complex.ofReal_mul, mul_zpow, show (k - 2 : ℤ) = (k - 1) + (k - 1) + (-k) by ring,
    zpow_add₀ huC, zpow_add₀ huC]
  ring

theorem fricke_mul_fricke (M : ℕ) [NeZero M] (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    W * W = Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.mk0 (-(M : ℝ)) (neg_ne_zero.mpr (by exact_mod_cast (NeZero.ne M)))) := by
  apply Units.ext
  rw [Units.val_mul, hW]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar, Matrix.natCast_apply]

theorem slash_fricke_slash_fricke (M : ℕ) [NeZero M] (k : ℤ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) (φ : UpperHalfPlane → ℂ) :
    (φ ∣[k] W) ∣[k] W = ((-(M : ℂ)) ^ (k - 2)) • φ := by
  rw [← SlashAction.slash_mul, fricke_mul_fricke M W hW, slash_scalar]
  simp

theorem exists_fricke_conj (M : ℕ) [NeZero M] (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0])
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ (g' : SL(2, ℤ)) (hg' : g' ∈ CongruenceSubgroup.Gamma0 M),
      (Matrix.SpecialLinearGroup.mapGL ℝ g' : GL (Fin 2) ℝ) * W = W * Matrix.SpecialLinearGroup.mapGL ℝ g ∧
      CohCarrier.gamma0Units M ⟨g', hg'⟩ = (CohCarrier.gamma0Units M ⟨g, hg⟩)⁻¹ := by

  have hc : (M : ℤ) ∣ g 1 0 := by
    rw [CongruenceSubgroup.Gamma0_mem] at hg
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hg
  obtain ⟨c₀, hc₀⟩ := hc
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at this
    exact this
  let g' : SL(2, ℤ) := ⟨!![g 1 1, -c₀; -((M : ℤ) * g 0 1), g 0 0], by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 0 1) * hc₀⟩
  have hg' : g' ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [g']
  refine ⟨g', hg', ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, hW, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
    have hc₀R : ((g 1 0 : ℤ) : ℝ) = (M : ℝ) * (c₀ : ℝ) := by exact_mod_cast hc₀
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g', Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, hc₀R] <;> ring
  ·
    apply Units.ext
    first
      | rfl
      | simp [CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map, g']

theorem mem_Gamma0_of_mem_Gamma1 {M : ℕ} {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma1 M) :
    g ∈ CongruenceSubgroup.Gamma0 M := by
  rw [CongruenceSubgroup.Gamma1_mem] at hg
  exact CongruenceSubgroup.Gamma0_mem.mpr hg.2.2

theorem gamma0Units_eq_one_of_mem_Gamma1 {M : ℕ} {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma1 M) :
    CohCarrier.gamma0Units M ⟨g, mem_Gamma0_of_mem_Gamma1 hg⟩ = 1 := by
  apply Units.ext
  rw [CohCarrier.val_gamma0Units, Units.val_one]
  exact ((CongruenceSubgroup.Gamma1_mem M g).mp hg).2.1

theorem mem_Gamma1_of_gamma0Units_eq_one {M : ℕ} {g : SL(2, ℤ)} (hg0 : g ∈ CongruenceSubgroup.Gamma0 M)
    (h1 : CohCarrier.gamma0Units M ⟨g, hg0⟩ = 1) : g ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  have hd : (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) = 1 := by
    have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) h1
    simp [CohCarrier.val_gamma0Units] at this
    exact this
  have hda := CohCarrier.Gamma0_d_mul_a M ⟨g, hg0⟩
  refine ⟨?_, hd, CongruenceSubgroup.Gamma0_mem.mp hg0⟩
  have : (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) * (((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod M) = 1 := hda
  rwa [hd, one_mul] at this

theorem Gamma1_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro g hg
  rw [CohCarrier.mem_GammaH_iff]
  exact ⟨mem_Gamma0_of_mem_Gamma1 hg, by rw [gamma0Units_eq_one_of_mem_Gamma1 hg]; exact one_mem H⟩

theorem slash_fricke_invariant (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) (φ : UpperHalfPlane → ℂ)
    (hφ : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), φ ∣[k] γ = φ) :
    ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), (φ ∣[k] W) ∣[k] γ = φ ∣[k] W := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨hg0, hgH⟩ := CohCarrier.mem_GammaH_iff.mp hg
  obtain ⟨g', hg', hmul, hunits⟩ := exists_fricke_conj M W hW g hg0
  have hg'H : g' ∈ CohCarrier.GammaH M H :=
    CohCarrier.mem_GammaH_iff.mpr ⟨hg', by rw [hunits]; exact H.inv_mem hgH⟩
  rw [← SlashAction.slash_mul, ← hmul, SlashAction.slash_mul, hφ _ (Subgroup.mem_map_of_mem _ hg'H)]

theorem slash_fricke_invariant_gamma1 (M : ℕ) [NeZero M] (k : ℤ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) (φ : UpperHalfPlane → ℂ)
    (hφ : ∀ γ ∈ (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)), φ ∣[k] γ = φ) :
    ∀ γ ∈ (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)), (φ ∣[k] W) ∣[k] γ = φ ∣[k] W := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨g', hg', hmul, hunits⟩ := exists_fricke_conj M W hW g (mem_Gamma0_of_mem_Gamma1 hg)
  have hg'1 : g' ∈ CongruenceSubgroup.Gamma1 M := by
    apply mem_Gamma1_of_gamma0Units_eq_one hg'
    rw [hunits, gamma0Units_eq_one_of_mem_Gamma1 hg, inv_one]
  rw [← SlashAction.slash_mul, ← hmul, SlashAction.slash_mul, hφ _ (Subgroup.mem_map_of_mem _ hg'1)]

theorem isCusp_smul_of_map_ratCast (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    (AQ : GL (Fin 2) ℚ) (A : GL (Fin 2) ℝ) (hA : Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) AQ = A)
    {c : OnePoint ℝ} (hc : IsCusp c Γ) : IsCusp (A • c) Γ := by
  classical
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  refine ⟨AQ • c₀, ?_⟩
  rw [← Rat.coe_castHom, OnePoint.map_smul, hA]

theorem exists_ratGL_fricke (M : ℕ) [NeZero M] (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ WQ : GL (Fin 2) ℚ, Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) WQ = W := by
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℚ), -1; (M : ℚ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]), ?_⟩
  apply Units.ext
  rw [hW]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem exists_ratGL_heckeMatrix (r : ℕ) (hr : r ≠ 0) (j : ℕ) :
    ∃ AQ : GL (Fin 2) ℚ, Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) AQ = ModularForm.heckeMatrix r j := by
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), (j : ℚ); 0, (r : ℚ)]
    (by rw [Matrix.det_fin_two_of]; simp [hr]), ?_⟩
  apply Units.ext
  rw [ModularForm.val_heckeMatrix hr]
  ext i j'
  fin_cases i <;> fin_cases j' <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem exists_modularForm_coe_eq_slash_fricke (M : ℕ) [NeZero M] {k : ℤ} (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0])
    (F : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ Z : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k,
      ⇑Z = (⇑F : UpperHalfPlane → ℂ) ∣[k] W := by
  obtain ⟨WQ, hWQ⟩ := exists_ratGL_fricke M W hW
  refine ⟨{ toFun := (⇑F : UpperHalfPlane → ℂ) ∣[k] W
            slash_action_eq' := fun γ hγ =>
              slash_fricke_invariant_gamma1 M k W hW ⇑F
                (fun γ hγ => SlashInvariantFormClass.slash_action_eq F γ hγ) γ hγ
            holo' := (ModularFormClass.holo F).slash k W
            bdd_at_cusps' := fun {c} hc =>
              (OnePoint.IsBoundedAt.smul_iff).mp
                (ModularFormClass.bdd_at_cusps F (isCusp_smul_of_map_ratCast _ WQ W hWQ hc)) }, rfl⟩

theorem mdifferentiable_finset_sum {ι : Type*} (s : Finset ι) (F : ι → UpperHalfPlane → ℂ)
    (hF : ∀ i ∈ s, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (F i)) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact mdifferentiable_const
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hF a (Finset.mem_insert_self a s)).add (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

theorem isBoundedAt_finset_sum {ι : Type*} (s : Finset ι) (F : ι → UpperHalfPlane → ℂ) (k : ℤ)
    {c : OnePoint ℝ} (hF : ∀ i ∈ s, c.IsBoundedAt (F i) k) : c.IsBoundedAt (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      intro g _
      rw [SlashAction.zero_slash]
      exact UpperHalfPlane.zero_form_isBoundedAtImInfty
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hF a (Finset.mem_insert_self a s)).add (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

theorem exists_gamma1_heckeMatrix_mul (M : ℕ) (r : ℕ) (hr : r ≠ 0) (hrM : r ∣ M)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma1 M) (j : ℕ) :
    haveI : NeZero r := ⟨hr⟩
    ∃ (g₁ : SL(2, ℤ)), g₁ ∈ CongruenceSubgroup.Gamma1 M ∧
      ModularForm.heckeMatrix r j * (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) =
        (Matrix.SpecialLinearGroup.mapGL ℝ g₁ : GL (Fin 2) ℝ) *
          ModularForm.heckeMatrix r ((((j : ℤ) + g 0 1 : ℤ) : ZMod r)).val := by
  haveI : NeZero r := ⟨hr⟩
  obtain ⟨m, hm⟩ := hrM

  have hg' := (CongruenceSubgroup.Gamma1_mem M g).mp hg
  have ha : (M : ℤ) ∣ g 0 0 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hg'.1, sub_self]
  have hd : (M : ℤ) ∣ g 1 1 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hg'.2.1, sub_self]
  have hc : (M : ℤ) ∣ g 1 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hg'.2.2
  obtain ⟨a₁, ha₁⟩ := ha
  obtain ⟨d₁, hd₁⟩ := hd
  obtain ⟨c₁, hc₁⟩ := hc
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at this
    exact this

  set jb : ℤ := (j : ℤ) + g 0 1 with hjb
  set j' : ℕ := ((jb : ℤ) : ZMod r).val with hj'def
  set t : ℤ := jb / r with htdef
  have hj'int : (j' : ℤ) = jb % r := by
    rw [hj'def, ZMod.val_intCast]
  have ht : jb = (r : ℤ) * t + j' := by rw [hj'int, htdef, Int.mul_ediv_add_emod]

  let a'' : ℤ := g 0 0 + j * g 1 0
  let b'' : ℤ := t + m * (j * d₁ - a₁ * j' - j * c₁ * j')
  let c'' : ℤ := r * g 1 0
  let d'' : ℤ := g 1 1 - g 1 0 * j'
  have hM : ((M : ℕ) : ℤ) = r * m := by rw [hm]; push_cast; ring
  have ha₁' : g 0 0 = 1 + (M : ℤ) * a₁ := by linear_combination ha₁
  have hd₁' : g 1 1 = 1 + (M : ℤ) * d₁ := by linear_combination hd₁
  have hbr : b'' * r = g 0 1 + j * g 1 1 - a'' * j' := by
    simp only [a'', b'']
    rw [ha₁', hd₁', hc₁, hM] at *
    linear_combination (-1 : ℤ) * ht
  have hdet'' : a'' * d'' - b'' * c'' = 1 := by
    have : b'' * c'' = (g 0 1 + j * g 1 1 - a'' * j') * g 1 0 := by
      simp only [c'']; rw [← hbr]; ring
    rw [this]
    simp only [a'', d'']
    linear_combination hdet
  let g₁ : SL(2, ℤ) := ⟨!![a'', b''; c'', d''], by rw [Matrix.det_fin_two_of]; exact hdet''⟩
  have hg₁ : g₁ ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · show ((a'' : ℤ) : ZMod M) = 1
      simp only [a'']; rw [ha₁', hc₁]; push_cast; simp
    · show ((d'' : ℤ) : ZMod M) = 1
      simp only [d'']; rw [hd₁', hc₁]; push_cast; simp
    · show ((c'' : ℤ) : ZMod M) = 0
      simp only [c'']; rw [hc₁]; push_cast; simp
  refine ⟨g₁, hg₁, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeMatrix hr, ModularForm.val_heckeMatrix hr,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  have hbrR : ((b'' : ℤ) : ℝ) * (r : ℝ) = ((g 0 1 : ℤ) : ℝ) + (j : ℝ) * ((g 1 1 : ℤ) : ℝ) - ((a'' : ℤ) : ℝ) * (j' : ℝ) := by
    exact_mod_cast hbr
  ext i i'
  simp only [a''] at hbrR; push_cast at hbrR
  fin_cases i <;> fin_cases i' <;>
    simp [g₁, a'', c'', d'', Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] <;> push_cast <;>
    (first | ring | skip)
  all_goals linear_combination (-1 : ℝ) * hbrR

theorem exists_modularForm_coe_eq_heckeU (M : ℕ) [NeZero M] {k : ℤ} (r : ℕ) (hr : r.Prime) (hrM : r ∣ M)
    (F : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ Y : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k,
      ⇑Y = ModularForm.heckeU k r ⇑F := by
  classical
  have hr0 : r ≠ 0 := hr.ne_zero
  haveI : NeZero r := ⟨hr0⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hr0

  have hsumZ : ∀ f : ℕ → UpperHalfPlane → ℂ,
      ∑ j ∈ Finset.range r, f j = ∑ x : ZMod r, f x.val := by
    intro f
    subst hn
    rw [← Fin.sum_univ_eq_sum_range]
    rfl
  refine ⟨{ toFun := ModularForm.heckeU k r ⇑F
            slash_action_eq' := ?_
            holo' := ?_
            bdd_at_cusps' := ?_ }, rfl⟩
  ·
    rintro _ ⟨g, hg, rfl⟩
    rw [ModularForm.heckeU_def, sum_slash]
    have hterm : ∀ j ∈ Finset.range r,
        ((⇑F : UpperHalfPlane → ℂ) ∣[k] ModularForm.heckeMatrix r j) ∣[k]
            (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) =
          (⇑F : UpperHalfPlane → ℂ) ∣[k] ModularForm.heckeMatrix r ((((j : ℤ) + g 0 1 : ℤ) : ZMod r)).val := by
      intro j _
      obtain ⟨g₁, hg₁, hmat⟩ := exists_gamma1_heckeMatrix_mul M r hr0 hrM g hg j
      rw [← SlashAction.slash_mul, hmat, SlashAction.slash_mul,
        SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ hg₁)]
    rw [Finset.sum_congr rfl hterm, hsumZ, hsumZ]

    set b : ZMod r := ((g 0 1 : ℤ) : ZMod r) with hb
    have : ∀ x : ZMod r, ((((x.val : ℕ) : ℤ) + g 0 1 : ℤ) : ZMod r) = x + b := by
      intro x; push_cast; rw [ZMod.natCast_zmod_val]
    simp_rw [this]
    exact Equiv.sum_comp (Equiv.addRight b) (fun y : ZMod r => (⇑F : UpperHalfPlane → ℂ) ∣[k] ModularForm.heckeMatrix r y.val)
  ·
    show MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeU k r ⇑F)
    rw [ModularForm.heckeU_def]
    exact mdifferentiable_finset_sum _ _ fun j _ => (ModularFormClass.holo F).slash k _
  ·
    intro c hc
    show OnePoint.IsBoundedAt c (ModularForm.heckeU k r ⇑F) k
    rw [ModularForm.heckeU_def]
    refine isBoundedAt_finset_sum _ _ k fun j _ => ?_
    obtain ⟨AQ, hAQ⟩ := exists_ratGL_heckeMatrix r hr0 j
    exact (OnePoint.IsBoundedAt.smul_iff).mp (ModularFormClass.bdd_at_cusps F (isCusp_smul_of_map_ratCast _ AQ _ hAQ hc))

theorem sum_range_eq_sum_zmod (r : ℕ) (hr : r ≠ 0) (f : ℕ → UpperHalfPlane → ℂ) :
    haveI : NeZero r := ⟨hr⟩
    ∑ j ∈ Finset.range r, f j = ∑ x : ZMod r, f x.val := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

theorem zmod_mul_eq_one_of_det {M r : ℕ} (hrM : r ∣ M) (γ : SL(2, ℤ)) (c₀ : ℤ) (hc₀ : γ 1 0 = (M : ℤ) * c₀) :
    ((γ 0 0 : ℤ) : ZMod r) * ((γ 1 1 : ℤ) : ZMod r) = 1 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at this
    exact this
  have hM0 : ((M : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff M r).mpr hrM
  have h := congrArg (fun z : ℤ => (z : ZMod r)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc₀] at h
  push_cast at h
  rw [hM0] at h
  linear_combination h

theorem exists_gamma0_transposeRep_mul (M : ℕ) [NeZero M] (r : ℕ) (hr : r.Prime) (hrM : r ∣ M)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (c₀ : ℤ) (hc₀ : γ 1 0 = (M : ℤ) * c₀) (j : ℕ) :
    haveI : NeZero r := ⟨hr.ne_zero⟩
    ∃ (γ'' : SL(2, ℤ)) (hγ'' : γ'' ∈ CongruenceSubgroup.Gamma0 M),
      CohCarrier.gamma0Units M ⟨γ'', hγ''⟩ = CohCarrier.gamma0Units M ⟨γ, hγ⟩ ∧
      ModularForm.heckeDiagMatrix r *
          (Matrix.SpecialLinearGroup.mapGL ℝ (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) :
            GL (Fin 2) ℝ) * (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
        (Matrix.SpecialLinearGroup.mapGL ℝ γ'' : GL (Fin 2) ℝ) *
          (ModularForm.heckeDiagMatrix r *
            (Matrix.SpecialLinearGroup.mapGL ℝ (Matrix.SpecialLinearGroup.transpose
              (ModularGroup.T ^ (M * ((((γ 0 0 : ℤ) * ((j : ℤ) * γ 0 0 + c₀) : ℤ) : ZMod r)).val))) : GL (Fin 2) ℝ)) := by
  have hr0 : r ≠ 0 := hr.ne_zero
  haveI : NeZero r := ⟨hr0⟩
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨m, hm⟩ := hrM
  have hM : ((M : ℕ) : ℤ) = r * m := by rw [hm]; push_cast; ring
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at this
    exact this
  set j' : ℕ := ((((γ 0 0 : ℤ) * ((j : ℤ) * γ 0 0 + c₀) : ℤ) : ZMod r)).val with hj'def
  have hj'cast : ((j' : ℕ) : ZMod r) = ((γ 0 0 : ℤ) : ZMod r) * ((j : ZMod r) * ((γ 0 0 : ℤ) : ZMod r) + (c₀ : ZMod r)) := by
    rw [hj'def, ZMod.natCast_zmod_val]; push_cast; ring

  let a'' : ℤ := γ 0 0 - M * j' * γ 0 1
  let b'' : ℤ := r * γ 0 1
  let c'' : ℤ := m * (j * γ 0 0 - j' * γ 1 1 - j * j' * M * γ 0 1 + c₀)
  let d'' : ℤ := M * j * γ 0 1 + γ 1 1
  have hcr : c'' * r = M * j * γ 0 0 + γ 1 0 - M * j' * (M * j * γ 0 1 + γ 1 1) := by
    simp only [c'']; rw [hc₀, hM]; ring
  have hdet'' : a'' * d'' - b'' * c'' = 1 := by
    have : b'' * c'' = γ 0 1 * (M * j * γ 0 0 + γ 1 0 - M * j' * (M * j * γ 0 1 + γ 1 1)) := by
      simp only [b'']; rw [← hcr]; ring
    rw [this]; simp only [a'', d'']; linear_combination hdet
  let γ'' : SL(2, ℤ) := ⟨!![a'', b''; c'', d''], by rw [Matrix.det_fin_two_of]; exact hdet''⟩

  have had : ((γ 0 0 : ℤ) : ZMod r) * ((γ 1 1 : ℤ) : ZMod r) = 1 := zmod_mul_eq_one_of_det ⟨m, hm⟩ γ c₀ hc₀
  have hM0 : ((M : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff M r).mpr ⟨m, hm⟩
  have hX : (r : ℤ) ∣ j * γ 0 0 - j' * γ 1 1 - j * j' * M * γ 0 1 + c₀ := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hj'cast]
    linear_combination (-((j : ZMod r) * ((γ 0 0 : ℤ) : ZMod r) + (c₀ : ZMod r))) * had +
      (-((j : ZMod r) * (((γ 0 0 : ℤ) : ZMod r) * ((j : ZMod r) * ((γ 0 0 : ℤ) : ZMod r) + (c₀ : ZMod r))) *
        ((γ 0 1 : ℤ) : ZMod r))) * hM0
  have hc''M : (M : ℤ) ∣ c'' := by
    obtain ⟨X, hXe⟩ := hX
    refine ⟨X, ?_⟩
    simp only [c'']; rw [hXe, hM]; ring
  have hγ'' : γ'' ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]
    show ((c'' : ℤ) : ZMod M) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc''M
  refine ⟨γ'', hγ'', ?_, ?_⟩
  ·
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
    show ((d'' : ℤ) : ZMod M) = ((γ 1 1 : ℤ) : ZMod M)
    simp only [d'']; push_cast; simp
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, ModularForm.val_heckeDiagMatrix hr0,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      coe_transpose_T_pow, coe_transpose_T_pow]
    have hcrR : ((c'' : ℤ) : ℝ) * (r : ℝ) =
        (M : ℝ) * (j : ℝ) * ((γ 0 0 : ℤ) : ℝ) + ((γ 1 0 : ℤ) : ℝ) -
          (M : ℝ) * (j' : ℝ) * ((M : ℝ) * (j : ℝ) * ((γ 0 1 : ℤ) : ℝ) + ((γ 1 1 : ℤ) : ℝ)) := by
      exact_mod_cast hcr
    have hγ''coe : (γ'' : Matrix (Fin 2) (Fin 2) ℤ) = !![a'', b''; c'', d''] := rfl
    rw [hγ''coe]
    ext i i'
    fin_cases i <;> fin_cases i' <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_cons, Matrix.head_fin_const] <;>
      simp [a'', b'', d''] <;> push_cast <;>
      (first | ring | skip)
    all_goals linear_combination (-1 : ℝ) * hcrR

theorem sum_slash_transpose_slash_SL_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (r : ℕ) (hr : r.Prime) (hrM : r ∣ M) (k : ℤ)
    (φ : UpperHalfPlane → ℂ)
    (hφ : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), φ ∣[k] γ = φ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    (∑ j ∈ Finset.range r,
        φ ∣[k] (ModularForm.heckeDiagMatrix r *
          (Matrix.SpecialLinearGroup.mapGL ℝ
            (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ))) ∣[k]
        (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
      ∑ j ∈ Finset.range r,
        (φ ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) ∣[k] (ModularForm.heckeDiagMatrix r *
          (Matrix.SpecialLinearGroup.mapGL ℝ
            (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ)) := by
  classical
  have hr0 : r ≠ 0 := hr.ne_zero
  haveI : NeZero r := ⟨hr0⟩
  haveI : Fact r.Prime := ⟨hr⟩

  have hc : (M : ℤ) ∣ γ 1 0 := by
    rw [CongruenceSubgroup.Gamma0_mem] at hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  obtain ⟨c₀, hc₀⟩ := hc

  set δ : ℕ → GL (Fin 2) ℝ := fun j => ModularForm.heckeDiagMatrix r *
      (Matrix.SpecialLinearGroup.mapGL ℝ
        (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ) with hδ
  rw [sum_slash]
  have hterm : ∀ j ∈ Finset.range r,
      (φ ∣[k] δ j) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
        (φ ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) ∣[k]
          δ ((((γ 0 0 : ℤ) * ((j : ℤ) * γ 0 0 + c₀) : ℤ) : ZMod r)).val := by
    intro j _
    obtain ⟨γ'', hγ'', hunits, hmat⟩ := exists_gamma0_transposeRep_mul M r hr hrM γ hγ c₀ hc₀ j
    rw [← SlashAction.slash_mul, hδ, hmat]
    simp only
    rw [CuspForm.slash_mapGL_eq_of_gamma0Units_eq k hφ ⟨γ'', hγ''⟩ ⟨γ, hγ⟩ hunits, SlashAction.slash_mul]
  rw [Finset.sum_congr rfl hterm, sum_range_eq_sum_zmod r hr0, sum_range_eq_sum_zmod r hr0]

  set A : ZMod r := ((γ 0 0 : ℤ) : ZMod r) * ((γ 0 0 : ℤ) : ZMod r) with hA
  set B : ZMod r := ((γ 0 0 : ℤ) : ZMod r) * (c₀ : ZMod r) with hB
  have hAne : A ≠ 0 := by
    have had : ((γ 0 0 : ℤ) : ZMod r) * ((γ 1 1 : ℤ) : ZMod r) = 1 := zmod_mul_eq_one_of_det hrM γ c₀ hc₀
    have ha : ((γ 0 0 : ℤ) : ZMod r) ≠ 0 := left_ne_zero_of_mul_eq_one had
    exact mul_ne_zero ha ha
  have hidx : ∀ x : ZMod r,
      ((((γ 0 0 : ℤ) * (((x.val : ℕ) : ℤ) * γ 0 0 + c₀) : ℤ) : ZMod r)) = A * x + B := by
    intro x; push_cast; rw [ZMod.natCast_zmod_val]; ring
  simp_rw [hidx]
  exact Equiv.sum_comp ((Equiv.mulLeft₀ A hAne).trans (Equiv.addRight B))
    (fun y : ZMod r => (φ ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) ∣[k] δ y.val)

theorem exists_ratGL_mapGL (γ : SL(2, ℤ)) :
    ∃ AQ : GL (Fin 2) ℚ, Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) AQ =
      (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) := by
  refine ⟨Matrix.SpecialLinearGroup.mapGL ℚ γ, ?_⟩
  apply Units.ext
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  ext i j
  simp [Matrix.map_apply]

theorem exists_modularForm_coe_eq_slash_of_mem_Gamma0 (M : ℕ) [NeZero M] {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ F' : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k,
      ⇑F' = (⇑F : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) := by
  obtain ⟨AQ, hAQ⟩ := exists_ratGL_mapGL γ
  refine ⟨{ toFun := (⇑F : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
            slash_action_eq' := ?_
            holo' := (ModularFormClass.holo F).slash k _
            bdd_at_cusps' := fun {c} hc =>
              (OnePoint.IsBoundedAt.smul_iff).mp
                (ModularFormClass.bdd_at_cusps F (isCusp_smul_of_map_ratCast _ AQ _ hAQ hc)) }, rfl⟩
  rintro _ ⟨g, hg, rfl⟩
  have hg0 := mem_Gamma0_of_mem_Gamma1 hg

  have hconj0 : γ * g * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 M :=
    (CongruenceSubgroup.Gamma0 M).mul_mem ((CongruenceSubgroup.Gamma0 M).mul_mem hγ hg0)
      ((CongruenceSubgroup.Gamma0 M).inv_mem hγ)
  have hconj1 : γ * g * γ⁻¹ ∈ CongruenceSubgroup.Gamma1 M := by
    apply mem_Gamma1_of_gamma0Units_eq_one hconj0
    have e : (⟨γ * g * γ⁻¹, hconj0⟩ : CongruenceSubgroup.Gamma0 M) =
        ⟨γ, hγ⟩ * ⟨g, hg0⟩ * (⟨γ, hγ⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, gamma0Units_eq_one_of_mem_Gamma1 hg, mul_one, mul_inv_cancel]
  have hmat : (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) * Matrix.SpecialLinearGroup.mapGL ℝ g =
      Matrix.SpecialLinearGroup.mapGL ℝ (γ * g * γ⁻¹) * Matrix.SpecialLinearGroup.mapGL ℝ γ := by
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  show ((⇑F : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) ∣[k]
      (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) = _
  rw [← SlashAction.slash_mul, hmat, SlashAction.slash_mul,
    SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ hconj1)]

end TTU
p2m_reactivate "P2MW.S_CuspForm_qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range.UTRatIhl P2MW.S_CuspForm_qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range.TTU"

namespace UTRatIhl
open UpperHalfPlane

theorem gamma1_le_gammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨_, h11, h10⟩ := hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
  refine ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    ext
    simp only [CohCarrier.gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one, CongruenceSubgroup.Gamma0Map]
    exact h11
  rw [this]
  exact one_mem H

def restrict1 {M : ℕ} {H : Subgroup (ZMod M)ˣ} {k : ℤ}
    (F : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := ⇑F
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq F A (Subgroup.map_mono (gamma1_le_gammaH M H) hA)
  holo' := ModularFormClass.holo F
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps F (hc.mono (Subgroup.map_mono (gamma1_le_gammaH M H)))

@[scoped simp] theorem coe_restrict1 {M : ℕ} {H : Subgroup (ZMod M)ˣ} {k : ℤ}
    (F : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) : (⇑(restrict1 F) : ℍ → ℂ) = ⇑F := rfl

def ofCusp {M : ℕ} {H : Subgroup (ZMod M)ˣ} {k : ℤ} (f : CuspForm (CohCarrier.GammaH M H) k) :
    ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := ⇑f
  slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ
  holo' := ModularFormClass.holo f
  bdd_at_cusps' := fun hc => ModularFormClass.bdd_at_cusps f hc

@[scoped simp] theorem coe_ofCusp {M : ℕ} {H : Subgroup (ZMod M)ˣ} {k : ℤ} (f : CuspForm (CohCarrier.GammaH M H) k) :
    (⇑(ofCusp f) : ℍ → ℂ) = ⇑f := rfl

theorem slash_invariant_of_mem_Gamma0 (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (φ : ℍ → ℂ) (hφ : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), φ ∣[k] γ = φ)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 M) :
    ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)),
      (φ ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ)) ∣[k] γ =
        φ ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) := by
  rintro _ ⟨h, hh, rfl⟩

  obtain ⟨⟨h0, hh0⟩, hhH, rfl⟩ := hh
  have hconj0 : g * h0 * g⁻¹ ∈ CongruenceSubgroup.Gamma0 M :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh0) (Subgroup.inv_mem _ hg)
  have hconj : g * h0 * g⁻¹ ∈ CohCarrier.GammaH M H := by
    refine ⟨⟨g * h0 * g⁻¹, hconj0⟩, ?_, rfl⟩
    have hhH' : CohCarrier.gamma0Units M ⟨h0, hh0⟩ ∈ H := hhH
    show CohCarrier.gamma0Units M ⟨g * h0 * g⁻¹, hconj0⟩ ∈ H
    have : (⟨g * h0 * g⁻¹, hconj0⟩ : CongruenceSubgroup.Gamma0 M) = ⟨g, hg⟩ * ⟨h0, hh0⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, mul_comm (CohCarrier.gamma0Units M ⟨g, hg⟩), mul_assoc, mul_inv_cancel, mul_one]
    exact hhH'
  have key := hφ _ ⟨_, hconj, rfl⟩
  show (φ ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ)) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ h0 : GL (Fin 2) ℝ) = _
  rw [← SlashAction.slash_mul, show (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) * Matrix.SpecialLinearGroup.mapGL ℝ h0 =
      Matrix.SpecialLinearGroup.mapGL ℝ (g * h0 * g⁻¹) * Matrix.SpecialLinearGroup.mapGL ℝ g by
        rw [← map_mul, ← map_mul]; congr 1; group,
    SlashAction.slash_mul, key]

end UTRatIhl
p2m_reactivate "P2MW.S_CuspForm_qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range.UTRatIhl P2MW.S_CuspForm_qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range.TTU"

namespace UTRatIhl
open UpperHalfPlane

theorem σ_apply_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < (g.det : ℝ)) (z : ℂ) : UpperHalfPlane.σ g z = z := by
  rw [UpperHalfPlane.σ, if_pos hg]; rfl

theorem sum_smul_slash {ι : Type*} (s : Finset ι) (k : ℤ) (A : GL (Fin 2) ℝ) (hA : 0 < (A.det : ℝ))
    (a : ι → ℂ) (f : ι → ℍ → ℂ) :
    (∑ i ∈ s, a i • f i) ∣[k] A = ∑ i ∈ s, a i • (f i ∣[k] A) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, SlashAction.add_slash, ih, ModularForm.smul_slash, σ_apply_of_det_pos hA]

theorem heckeU_sum_smul {ι : Type*} (s : Finset ι) (k : ℤ) (r : ℕ) (a : ι → ℂ) (f : ι → ℍ → ℂ) :
    ModularForm.heckeU k r (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i • ModularForm.heckeU k r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ModularForm.heckeU_add, ModularForm.heckeU_smul, ih]

theorem det_fricke_pos (M : ℕ) [NeZero M] (W : GL (Fin 2) ℝ) (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    0 < (W.det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, hW, Matrix.det_fin_two_of]
  have : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  linarith

theorem det_mapGL_pos (γ : SL(2, ℤ)) : 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ).det : ℝ) := by
  simp [Matrix.SpecialLinearGroup.mapGL, Matrix.GeneralLinearGroup.val_det_apply]

end UTRatIhl
p2m_reactivate "P2MW.S_CuspForm_qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range.UTRatIhl P2MW.S_CuspForm_qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range.TTU"

open UTRatIhl UpperHalfPlane in

theorem UTRatIhl.qCoeff_sum_slash_transpose_mem_range
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (r : ℕ) (hr : r.Prime) (hrM : r ∣ M) (k : ℤ)
    (g : CuspForm (CohCarrier.GammaH M H) k)
    (hg : ∀ n : ℕ, ModularFormClass.qCoeff (⇑g) n ∈ (algebraMap ℚ ℂ).range) (n : ℕ) :
    ModularFormClass.qCoeff
        (∑ j ∈ Finset.range r,
          (⇑g) ∣[k] (ModularForm.heckeDiagMatrix r *
            (Matrix.SpecialLinearGroup.mapGL ℝ
              (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ))) n ∈
      (algebraMap ℚ ℂ).range := by
  classical

  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  let W : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simpa using hM0)
  have hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl
  have hWpos := det_fricke_pos M W hW
  let ι : AlgebraicClosure ℚ →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := AlgebraicClosure ℚ)).toRingHom
  have hι : Function.Injective ι := ι.injective
  have hΓ1 := one_mem_strictPeriods_Gamma1 M

  set UrT : (ℍ → ℂ) → (ℍ → ℂ) := fun φ => ∑ j ∈ Finset.range r,
      φ ∣[k] (ModularForm.heckeDiagMatrix r *
        (Matrix.SpecialLinearGroup.mapGL ℝ (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ)) with hUrT
  show ModularFormClass.qCoeff (UrT ⇑g) n ∈ _

  have hginv : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), (⇑g : ℍ → ℂ) ∣[k] γ = ⇑g :=
    fun γ hγ => SlashInvariantFormClass.slash_action_eq g γ hγ
  have hgrat : ∀ m : ℕ, ∃ q : ℚ, (qExpansion 1 (⇑(restrict1 (ofCusp g)) : ℍ → ℂ)).coeff m = (q : ℂ) := by
    intro m
    obtain ⟨q, hq⟩ := hg m
    exact ⟨q, by rw [← eq_ratCast (algebraMap ℚ ℂ) q, hq]; rfl⟩

  have hgrat' : ∀ m : ℕ, ∃ q : ℚ, (qExpansion 1 (⇑(ofCusp g) : ℍ → ℂ)).coeff m = (q : ℂ) := hgrat
  obtain ⟨n₀, c, G, P, hGP, hsum⟩ :=
    ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion M H (ofCusp g) hgrat' ι W hW
  rw [coe_ofCusp] at hsum

  choose Y hY using fun i => TTU.exists_modularForm_coe_eq_heckeU M r hr hrM (restrict1 (G i))
  have hYrat : ∀ i (m : ℕ), ∃ q : ℚ, (qExpansion 1 (⇑(Y i) : ℍ → ℂ)).coeff m = (q : ℂ) := by
    intro i m
    refine ⟨((PowerSeries.coeff (r * m) (P i) : ℤ) : ℚ), ?_⟩
    rw [hY, ModularFormClass.qExpansion_heckeU_eq_heckeU (restrict1 (G i)) hΓ1 hr.ne_zero, PowerSeries.coeff_heckeU,
      coe_restrict1, ← (hGP i).coeff]
    push_cast; rfl
  choose Z hZ using fun i => TTU.exists_modularForm_coe_eq_slash_fricke M W hW (Y i)

  choose a ha hlaw using fun i => ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0 M (Y i) (hYrat i) ι W hW
  obtain ⟨a₀, ha₀, hlaw₀⟩ := ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0 M (restrict1 (ofCusp g)) hgrat ι W hW
  simp only [coe_restrict1, coe_ofCusp] at ha₀ hlaw₀

  have hXsum : (ModularForm.heckeU k r ((⇑g : ℍ → ℂ) ∣[k] W)) ∣[k] W = ⇑(∑ i, ι (c i) • Z i) := by
    rw [coe_sum_smul, hsum, heckeU_sum_smul, sum_smul_slash _ _ _ hWpos]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hZ i, hY i, coe_restrict1]
  have hκX : ((-(M : ℂ)) ^ (k - 2)) • UrT ⇑g = ModularForm.heckeU k r ((⇑g : ℍ → ℂ) ∣[k] W) ∣[k] W := by
    rw [← TTU.slash_fricke_slash_fricke M k W hW (UrT ⇑g), hUrT,
      TTU.sum_slash_transpose_slash_fricke_eq_heckeU_slash_fricke M H r hr.ne_zero k W hW ⇑g hginv]

  have hXcoeff : ∀ m : ℕ, (qExpansion 1 (⇑(∑ i, ι (c i) • Z i) : ℍ → ℂ)).coeff m = ι (∑ i, c i * a i m) := by
    intro m
    rw [qExpansion_coe_sum_smul hΓ1, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.coeff_smul, smul_eq_mul, map_mul, hZ i, ha i m]

  have ha₀P : ∀ m : ℕ, a₀ m = ∑ i, c i * ((PowerSeries.coeff m (P i) : ℤ) : AlgebraicClosure ℚ) := by
    intro m
    apply hι
    rw [← ha₀ m, hsum, show (∑ i, ι (c i) • (⇑(G i) : ℍ → ℂ)) = ⇑(∑ i, ι (c i) • restrict1 (G i)) by
      rw [coe_sum_smul]; rfl, qExpansion_coe_sum_smul hΓ1, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.coeff_smul, smul_eq_mul, map_mul, coe_restrict1, ← (hGP i).coeff, map_intCast]

  have hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ (∑ i, c i * a i n) = ∑ i, c i * a i n := by
    intro σ
    obtain ⟨cσ, hcop, hζ⟩ := exists_coprime_forall_pow_eq_one_apply_eq_pow M σ
    obtain ⟨γ, hγ, hγc⟩ := exists_mem_Gamma0_apply_eq M hcop
    obtain ⟨γ', hγ', hWγ, hunits⟩ := TTU.exists_fricke_conj M W hW γ hγ
    have hco : (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) := rfl

    obtain ⟨GW, hGW⟩ := TTU.exists_modularForm_coe_eq_slash_fricke M W hW (restrict1 (ofCusp g))
    obtain ⟨GWγ, hGWγ⟩ := TTU.exists_modularForm_coe_eq_slash_of_mem_Gamma0 M GW γ hγ
    have hA : (∑ i, ι (σ (c i)) • restrict1 (G i)) = GWγ := by
      apply eq_of_qExpansion_eq hΓ1
      ext m
      rw [qExpansion_coe_sum_smul hΓ1, map_sum, hGWγ, hGW, coe_restrict1, coe_ofCusp, hco, hlaw₀ σ cσ hζ γ hγ hγc m, ha₀P m,
        map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [PowerSeries.coeff_smul, smul_eq_mul, coe_restrict1, ← (hGP i).coeff, map_mul, map_mul, map_intCast, map_intCast]
    have hAfun : (∑ i, ι (σ (c i)) • (⇑(G i) : ℍ → ℂ)) =
        ((⇑g : ℍ → ℂ) ∣[k] W) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) := by
      have := congrArg (fun F : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k => (⇑F : ℍ → ℂ)) hA
      simpa only [coe_sum_smul, coe_restrict1, hGWγ, hGW, coe_ofCusp] using this

    choose Z' hZ' using fun i => TTU.exists_modularForm_coe_eq_slash_of_mem_Gamma0 M (Z i) γ hγ
    have hφ' := slash_invariant_of_mem_Gamma0 M H k ⇑g hginv γ' hγ'
    have h3 := TTU.sum_slash_transpose_slash_fricke_eq_heckeU_slash_fricke M H r hr.ne_zero k W hW _ hφ'
    have h4 := TTU.slash_fricke_slash_fricke M k W hW
      (UrT ((⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ)))
    have h5 : UrT ((⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ)) ∣[k]
        (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = UrT ⇑g := by
      rw [hUrT]
      dsimp only
      rw [TTU.sum_slash_transpose_slash_SL_eq M H r hr hrM k _ hφ' γ hγ, ← SlashAction.slash_mul, ← map_mul]
      have hmem : γ' * γ ∈ CohCarrier.GammaH M H := by
        refine ⟨⟨γ' * γ, Subgroup.mul_mem _ hγ' hγ⟩, ?_, rfl⟩
        show CohCarrier.gamma0Units M ⟨γ' * γ, _⟩ ∈ H
        have : (⟨γ' * γ, Subgroup.mul_mem _ hγ' hγ⟩ : CongruenceSubgroup.Gamma0 M) = ⟨γ', hγ'⟩ * ⟨γ, hγ⟩ := rfl
        rw [this, map_mul, hunits, inv_mul_cancel]; exact one_mem H
      rw [hginv _ ⟨_, hmem, rfl⟩]
    have hB : (∑ i, ι (σ (c i)) • (⇑(Z' i) : ℍ → ℂ)) = ModularForm.heckeU k r ((⇑g : ℍ → ℂ) ∣[k] W) ∣[k] W := by
      have h1 : (∑ i, ι (σ (c i)) • (⇑(Z' i) : ℍ → ℂ)) =
          ((ModularForm.heckeU k r (∑ i, ι (σ (c i)) • (⇑(G i) : ℍ → ℂ))) ∣[k] W) ∣[k]
            (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) := by
        rw [heckeU_sum_smul, sum_smul_slash _ _ _ hWpos, sum_smul_slash _ _ _ (det_mapGL_pos γ)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hZ' i, hZ i, hY i, coe_restrict1]
      have h2 : ((⇑g : ℍ → ℂ) ∣[k] W) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
          ((⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ)) ∣[k] W := by
        rw [← SlashAction.slash_mul, ← SlashAction.slash_mul, hWγ]
      rw [h1, hAfun, h2, ← h3]
      rw [hUrT] at h4 h5
      dsimp only at h4 h5
      rw [h4, ModularForm.smul_slash, σ_apply_of_det_pos (det_mapGL_pos γ), h5]
      rw [hUrT] at hκX
      exact hκX

    apply hι
    rw [map_sum, map_sum]
    calc ∑ i, ι (σ (c i * a i n)) = ∑ i, ι (σ (c i)) * (qExpansion 1 (⇑(Z' i) : ℍ → ℂ)).coeff n := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, map_mul, hZ' i, hZ i, hco, hlaw i σ cσ hζ γ hγ hγc n]
      _ = (qExpansion 1 (⇑(∑ i, ι (σ (c i)) • Z' i) : ℍ → ℂ)).coeff n := by
          rw [qExpansion_coe_sum_smul hΓ1, map_sum]
          simp only [PowerSeries.coeff_smul, smul_eq_mul]
      _ = (qExpansion 1 (⇑(∑ i, ι (c i) • Z i) : ℍ → ℂ)).coeff n := by rw [coe_sum_smul, hB, hXsum]
      _ = ι (∑ i, c i * a i n) := by rw [hXcoeff]

  obtain ⟨q, hq⟩ := mem_range_algebraMap_of_forall_algEquiv _ hfix
  have hκ0 : ((-(M : ℂ)) ^ (k - 2)) ≠ 0 := zpow_ne_zero _ (neg_ne_zero.mpr (by exact_mod_cast NeZero.ne M))
  have hUrTg : UrT ⇑g = ((-(M : ℂ)) ^ (k - 2))⁻¹ • (⇑(∑ i, ι (c i) • Z i) : ℍ → ℂ) := by
    rw [← hXsum, ← hκX, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
  refine ⟨((-(M : ℚ)) ^ (k - 2))⁻¹ * q, ?_⟩
  show _ = (qExpansion 1 (UrT ⇑g)).coeff n
  rw [hUrTg, ModularForm.qExpansion_smul one_pos hΓ1 _ (∑ i, ι (c i) • Z i), PowerSeries.coeff_smul, hXcoeff, ← hq,
    smul_eq_mul, map_mul, eq_ratCast]
  congr 1
  · push_cast; rfl
  · show algebraMap ℚ ℂ q = ι (algebraMap ℚ (AlgebraicClosure ℚ) q)
    rw [eq_ratCast, eq_ratCast, map_ratCast]

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (r : ℕ) (hr : r.Prime) (hrM : r ∣ M) (k : ℤ)
    (g : CuspForm (CohCarrier.GammaH M H) k)
    (hg : ∀ n : ℕ, ModularFormClass.qCoeff (⇑g) n ∈ (algebraMap ℚ ℂ).range) :
    ∀ n : ℕ, ModularFormClass.qCoeff
        (∑ j ∈ Finset.range r,
          (⇑g) ∣[k] (ModularForm.heckeDiagMatrix r *
            (Matrix.SpecialLinearGroup.mapGL ℝ
              (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ))) n ∈
      (algebraMap ℚ ℂ).range := by
  intro n
  exact UTRatIhl.qCoeff_sum_slash_transpose_mem_range M H r hr hrM k g hg n

end S_CuspForm_qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range
end P2MW
export P2MW.S_CuspForm_qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range (solution)
