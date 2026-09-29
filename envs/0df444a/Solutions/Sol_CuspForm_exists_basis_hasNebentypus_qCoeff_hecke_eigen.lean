-- Prove2me | solution 1 for CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0b39f180-7bbd-5335-9b94-676fd8aec7df

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_PeterssonOn
import Theorems.Thm_ModularForm_heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0
import Theorems.Thm_CuspForm_peterssonOn_add_smul_conj
import Theorems.Thm_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff
import Theorems.Thm_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeT
import Theorems.Thm_UpperHalfPlane_qCoeff_heckeU
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero"

set_option autoImplicit false

open CongruenceSubgroup ModularForm UpperHalfPlane Filter Function
open scoped ModularForm UpperHalfPlane MatrixGroups ComplexConjugate

noncomputable section

namespace SimulEigen

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

structure IsPosDefHerm (B : W → W → ℂ) : Prop where
  add_right : ∀ x y z, B x (y + z) = B x y + B x z
  smul_right : ∀ x (c : ℂ) y, B x (c • y) = c * B x y
  conj_symm : ∀ x y, conj (B y x) = B x y
  definite : ∀ x, B x x = 0 → x = 0

namespace IsPosDefHerm

variable {B : W → W → ℂ} (hB : IsPosDefHerm B)
include hB

theorem add_left (x y z : W) : B (x + y) z = B x z + B y z := by
  rw [← hB.conj_symm, hB.add_right, map_add, hB.conj_symm, hB.conj_symm]

theorem smul_left (c : ℂ) (x y : W) : B (c • x) y = conj c * B x y := by
  rw [← hB.conj_symm, hB.smul_right, map_mul, hB.conj_symm]

theorem zero_right (x : W) : B x 0 = 0 := by
  have h := hB.add_right x 0 0
  rw [add_zero] at h
  have h2 : B x 0 + B x 0 - B x 0 = B x 0 - B x 0 := by rw [← h]
  simpa using h2

theorem sub_right (x y z : W) : B x (y - z) = B x y - B x z := by
  rw [sub_eq_add_neg, hB.add_right, ← neg_one_smul ℂ z, hB.smul_right]; ring

theorem sub_left (x y z : W) : B (x - y) z = B x z - B y z := by
  rw [← hB.conj_symm, hB.sub_right, map_sub, hB.conj_symm, hB.conj_symm]

theorem ker_sq (S : W →ₗ[ℂ] W) (hS : ∀ x y, B (S x) y = B x (S y)) (μ : ℂ) (v : W)
    (h : (S - μ • 1) ((S - μ • 1) v) = 0) : (S - μ • 1) v = 0 := by
  set A : W →ₗ[ℂ] W := S - μ • 1 with hA
  set A' : W →ₗ[ℂ] W := S - conj μ • 1 with hA'
  have hAadj : ∀ x y, B (A x) y = B x (A' y) := by
    intro x y
    simp only [hA, hA', LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [hB.sub_left, hB.sub_right, hB.smul_left, hB.smul_right, hS]
  have hA'adj : ∀ x y, B (A' x) y = B x (A y) := by
    intro x y
    simp only [hA, hA', LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [hB.sub_left, hB.sub_right, hB.smul_left, hB.smul_right, hS, Complex.conj_conj]
  have hcomm : ∀ x, A (A' x) = A' (A x) := by
    intro x
    simp only [hA, hA', LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, map_smul]
    module
  set w := A v with hw
  have h1 : A' w = 0 := by
    apply hB.definite
    rw [hA'adj, hcomm, show A w = 0 from h, map_zero, hB.zero_right]
  apply hB.definite
  rw [hAadj, h1, hB.zero_right]

theorem maxGenEigenspace_eq (S : W →ₗ[ℂ] W) (hS : ∀ x y, B (S x) y = B x (S y)) (μ : ℂ) :
    Module.End.maxGenEigenspace (S : Module.End ℂ W) μ = Module.End.eigenspace (S : Module.End ℂ W) μ := by
  apply le_antisymm _ Module.End.eigenspace_le_maxGenEigenspace
  have aux : ∀ (n : ℕ) (v : W), ((S - μ • 1) ^ n) v = 0 → (S - μ • 1) v = 0 := by
    intro n
    induction n with
    | zero => intro v hn; simp at hn; simp [hn]
    | succ n ih =>
      intro v hn
      rw [pow_succ, Module.End.mul_apply] at hn
      exact hB.ker_sq S hS μ v (ih _ hn)
  intro v hv
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨n, hn⟩ := hv
  rw [Module.End.mem_eigenspace_iff]
  have h := aux n v hn
  simpa [sub_eq_zero] using h

theorem span_common_eigen [FiniteDimensional ℂ W] {ι : Type*} (T : ι → W →ₗ[ℂ] W)
    (hcomm : ∀ i j, Commute (T i) (T j)) (hT : ∀ i x y, B (T i x) y = B x (T i y)) :
    Submodule.span ℂ {v : W | ∀ i, ∃ c : ℂ, T i v = c • v} = ⊤ := by
  have key : ⨆ χ : ι → ℂ, ⨅ i, Module.End.maxGenEigenspace (T i : Module.End ℂ W) (χ i) = ⊤ := by
    refine Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (fun i => (T i : Module.End ℂ W)) (fun i j _ => hcomm i j) fun i => ?_
    exact Module.End.iSup_maxGenEigenspace_eq_top _
  rw [eq_top_iff, ← key, iSup_le_iff]
  intro χ v hv
  refine Submodule.subset_span fun i => ⟨χ i, ?_⟩
  have hvi : v ∈ Module.End.maxGenEigenspace (T i : Module.End ℂ W) (χ i) := (Submodule.mem_iInf _).mp hv i
  rw [hB.maxGenEigenspace_eq (T i) (hT i)] at hvi
  exact Module.End.mem_eigenspace_iff.mp hvi

end IsPosDefHerm

end SimulEigen

namespace SSbasis

variable {N : ℕ}

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

theorem det_mod (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hγ
  have := congrArg (Int.cast : ℤ → ZMod N) (det_eq γ)
  push_cast at this
  rw [hc] at this
  linear_combination this

def dd (γ : SL(2, ℤ)) : ZMod N := ((γ 1 1 : ℤ) : ZMod N)

theorem dd_mul {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 N) (h₂ : γ₂ ∈ Gamma0 N) :
    dd (N := N) (γ₁ * γ₂) = dd (N := N) γ₁ * dd γ₂ := by
  have := map_mul (Gamma0Map N) ⟨γ₁, h₁⟩ ⟨γ₂, h₂⟩
  exact this

theorem dd_one : dd (N := N) 1 = 1 := by simp [dd]

theorem isUnit_dd {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) : IsUnit (dd (N := N) γ) :=
  IsUnit.of_mul_eq_one _ (by rw [dd, mul_comm]; exact det_mod γ hγ)

theorem mem_Gamma1_iff_dd {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    γ ∈ Gamma1 N ↔ dd (N := N) γ = 1 := by
  rw [Gamma1_mem, dd]
  constructor
  · rintro ⟨-, h, -⟩; simpa using h
  · intro hd
    have ha : ((γ 0 0 : ℤ) : ZMod N) = 1 := by
      have := det_mod γ hγ; rw [hd, mul_one] at this; exact this
    exact ⟨by simpa using ha, by simpa using hd, by simpa using Gamma0_mem.mp hγ⟩

theorem dd_eq_one_of_mem_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) : dd (N := N) γ = 1 :=
  (mem_Gamma1_iff_dd (Gamma1_in_Gamma0 N hγ)).mp hγ

theorem mul_inv_mem_Gamma1 {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 N) (h₂ : γ₂ ∈ Gamma0 N)
    (h : dd (N := N) γ₁ = dd γ₂) : γ₂ * γ₁⁻¹ ∈ Gamma1 N := by
  have hmem : γ₂ * γ₁⁻¹ ∈ Gamma0 N := mul_mem h₂ (inv_mem h₁)
  rw [mem_Gamma1_iff_dd hmem]
  have hprod : dd (N := N) (γ₂ * γ₁⁻¹) * dd (N := N) γ₁ = dd γ₂ := by
    rw [← dd_mul hmem h₁, inv_mul_cancel_right]
  rw [h] at hprod
  exact (isUnit_dd h₂).mul_left_injective (hprod.trans (one_mul _).symm)

theorem conj_mem_Gamma1 {σ γ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 N) (hγ : γ ∈ Gamma1 N) :
    σ * γ * σ⁻¹ ∈ Gamma1 N := by
  have hγ0 : γ ∈ Gamma0 N := Gamma1_in_Gamma0 N hγ
  have hmem : σ * γ * σ⁻¹ ∈ Gamma0 N := mul_mem (mul_mem hσ hγ0) (inv_mem hσ)
  rw [mem_Gamma1_iff_dd hmem]
  have h1 : dd (N := N) γ = 1 := (mem_Gamma1_iff_dd hγ0).mp hγ
  have hprod : dd (N := N) (σ * γ * σ⁻¹) * dd (N := N) σ = dd σ := by
    rw [← dd_mul hmem hσ, inv_mul_cancel_right, dd_mul hσ hγ0, h1, mul_one]
  exact (isUnit_dd hσ).mul_left_injective (hprod.trans (one_mul _).symm)

theorem exists_lift (u : (ZMod N)ˣ) [NeZero N] :
    ∃ σ : SL(2, ℤ), σ ∈ Gamma0 N ∧ dd (N := N) σ = (u : ZMod N) := by
  have hn : (u : ZMod N).val.Coprime N := ZMod.val_coe_unit_coprime u
  obtain ⟨a, b, hab⟩ : IsCoprime ((u : ZMod N).val : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.mpr hn
  refine ⟨⟨!![a, -b; (N : ℤ), ((u : ZMod N).val : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination hab
  · rw [Gamma0_mem]; simp
  · simp [dd]

section Slash

variable {k : ℤ}

theorem sl_slash (f : ℍ → ℂ) (γ : SL(2, ℤ)) :
    f ∣[k] γ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) := rfl

theorem slash_mem (g : CuspForm Γ₁(N) k) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) :
    (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑g :=
  SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)

theorem hasNebentypus_iff (ε : DirichletCharacter ℂ N) (g : CuspForm Γ₁(N) k) :
    CuspForm.HasNebentypus ε g ↔ ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N →
      (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ε (dd γ) • ⇑g := by
  constructor
  · intro h γ hγ
    funext τ
    have hpt := h γ hγ τ
    rw [← sl_slash, SL_slash_apply, Pi.smul_apply, smul_eq_mul]
    have hden : denom (Matrix.SpecialLinearGroup.toGL
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ)
        = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
      simp [denom]
    rw [hden]
    have hne : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
      rw [← hden]; exact UpperHalfPlane.denom_ne_zero _ τ
    rw [hpt, dd, zpow_neg]
    field_simp
  · intro h γ hγ τ
    have hslash := congrFun (h γ hγ) τ
    rw [← sl_slash, SL_slash_apply, Pi.smul_apply, smul_eq_mul] at hslash
    have hden : denom (Matrix.SpecialLinearGroup.toGL
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ)
        = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
      simp [denom]
    rw [hden] at hslash
    have hne : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
      rw [← hden]; exact UpperHalfPlane.denom_ne_zero _ τ
    have hzk : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) ≠ 0 := zpow_ne_zero _ hne
    have key : g (γ • τ) =
        ε (dd (N := N) γ) * g τ * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hzk]
      exact hslash
    rw [key, ← zpow_neg, neg_neg, dd]
    ring

theorem slash_eq_of_dd_eq (g : CuspForm Γ₁(N) k) {σ σ' : SL(2, ℤ)} (hσ : σ ∈ Gamma0 N)
    (hσ' : σ' ∈ Gamma0 N) (h : dd (N := N) σ = dd σ') :
    (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
      = (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ' : GL (Fin 2) ℝ) := by
  have hmem := mul_inv_mem_Gamma1 hσ hσ' h
  conv_rhs => rw [show σ' = (σ' * σ⁻¹) * σ by rw [inv_mul_cancel_right], map_mul,
    SlashAction.slash_mul, slash_mem g hmem]

end Slash

section Diamond

variable [NeZero N] {k : ℤ}

def diamond (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) : CuspForm Γ₁(N) k →ₗ[ℂ] CuspForm Γ₁(N) k where
  toFun g :=
    { toFun := (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
      slash_action_eq' := by
        intro A hA
        obtain ⟨γ, hγ, rfl⟩ := hA
        change ((⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)) ∣[k]
          (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = _
        rw [← SlashAction.slash_mul, ← map_mul,
          show σ * γ = (σ * γ * σ⁻¹) * σ by rw [inv_mul_cancel_right], map_mul,
          SlashAction.slash_mul, slash_mem g (conj_mem_Gamma1 hσ hγ)]
      holo' := (CuspFormClass.holo g).slash k _
      zero_at_cusps' := by
        intro c hc A hA
        have hσSL : (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨σ, rfl⟩
        have hc' : IsCusp ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) • c) Γ₁(N) := by
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
          exact hc.smul_of_mem hσSL
        have := (OnePoint.IsZeroAt.smul_iff (g := (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ))
          (c := c) (f := (⇑g : ℍ → ℂ)) (k := k)).mp (CuspFormClass.zero_at_cusps g hc')
        exact this A hA }
  map_add' g h := by
    apply DFunLike.coe_injective
    change ((⇑(g + h) : ℍ → ℂ)) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
      = (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
        + (⇑h : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
    rw [CuspForm.coe_add, SlashAction.add_slash]
  map_smul' c g := by
    apply DFunLike.coe_injective
    change ((⇑(c • g) : ℍ → ℂ)) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
      = c • ((⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ))
    rw [CuspForm.IsGLPos.coe_smul, ← sl_slash, ModularForm.SL_smul_slash, sl_slash]

theorem coe_diamond (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (g : CuspForm Γ₁(N) k) :
    (⇑(diamond σ hσ g) : ℍ → ℂ)
      = (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) := rfl

def nebSpace (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) :
    Submodule ℂ (CuspForm Γ₁(N) k) where
  carrier := {g | CuspForm.HasNebentypus ε g}
  zero_mem' := by
    intro γ _ τ
    simp
  add_mem' := by
    intro g h hg hh
    rw [Set.mem_setOf_eq, hasNebentypus_iff] at hg hh ⊢
    intro γ hγ
    rw [CuspForm.coe_add, SlashAction.add_slash, hg γ hγ, hh γ hγ, smul_add]
  smul_mem' := by
    intro c g hg
    rw [Set.mem_setOf_eq, hasNebentypus_iff] at hg ⊢
    intro γ hγ
    rw [CuspForm.IsGLPos.coe_smul, ← sl_slash, ModularForm.SL_smul_slash, sl_slash, hg γ hγ,
      smul_comm]

theorem mem_nebSpace {ε : DirichletCharacter ℂ N} {g : CuspForm Γ₁(N) k} :
    g ∈ nebSpace N k ε ↔ CuspForm.HasNebentypus ε g := Iff.rfl

def lift (u : (ZMod N)ˣ) : SL(2, ℤ) := (exists_lift (N := N) u).choose

theorem lift_mem (u : (ZMod N)ˣ) : lift (N := N) u ∈ Gamma0 N := (exists_lift (N := N) u).choose_spec.1

theorem dd_lift (u : (ZMod N)ˣ) : dd (N := N) (lift u) = (u : ZMod N) :=
  (exists_lift (N := N) u).choose_spec.2

def proj (ε : DirichletCharacter ℂ N) (g : CuspForm Γ₁(N) k) : CuspForm Γ₁(N) k :=
  ((N.totient : ℂ))⁻¹ • ∑ u : (ZMod N)ˣ, ε ((u⁻¹ : (ZMod N)ˣ) : ZMod N) • diamond (lift u) (lift_mem u) g

omit [NeZero N] in
theorem coe_sum {ι : Type*} (s : Finset ι) (F : ι → CuspForm Γ₁(N) k) :
    (⇑(∑ i ∈ s, F i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(F i) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.coe_add, ih]

theorem coe_proj (ε : DirichletCharacter ℂ N) (g : CuspForm Γ₁(N) k) :
    (⇑(proj ε g) : ℍ → ℂ) = ((N.totient : ℂ))⁻¹ •
      ∑ u : (ZMod N)ˣ, ε ((u⁻¹ : (ZMod N)ˣ) : ZMod N) •
        ((⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (lift u) : GL (Fin 2) ℝ)) := by
  rw [proj, CuspForm.IsGLPos.coe_smul, coe_sum]
  rfl

theorem proj_mem (ε : DirichletCharacter ℂ N) (g : CuspForm Γ₁(N) k) : proj ε g ∈ nebSpace N k ε := by
  rw [mem_nebSpace, hasNebentypus_iff]
  intro γ hγ
  set d₀ : (ZMod N)ˣ := (isUnit_dd hγ).unit with hd₀
  have hd₀' : (d₀ : ZMod N) = dd γ := (isUnit_dd hγ).unit_spec
  rw [coe_proj, ModularForm.smul_slash, SlashAction.sum_slash]

  have hσ : ∀ c : ℂ, UpperHalfPlane.σ (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) c = c := by
    intro c
    rw [UpperHalfPlane.σ, if_pos (by simp)]
    rfl
  simp_rw [hσ, ModularForm.smul_slash, hσ, ← SlashAction.slash_mul, ← map_mul]

  have hstep : ∀ u : (ZMod N)ˣ,
      (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (lift u * γ) : GL (Fin 2) ℝ)
        = (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (lift (u * d₀)) : GL (Fin 2) ℝ) := by
    intro u
    apply slash_eq_of_dd_eq g (mul_mem (lift_mem u) hγ) (lift_mem _)
    rw [dd_mul (lift_mem u) hγ, dd_lift, dd_lift, ← hd₀', Units.val_mul]
  simp_rw [hstep]
  rw [smul_comm]
  congr 1

  rw [Finset.smul_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight d₀) _ _ fun u => ?_)
  simp only [Equiv.coe_mulRight]
  rw [smul_smul]
  congr 1
  rw [show (u⁻¹ : (ZMod N)ˣ) = d₀ * (u * d₀)⁻¹ by group, Units.val_mul, map_mul, hd₀']

theorem sum_proj (g : CuspForm Γ₁(N) k) : ∑ ε : DirichletCharacter ℂ N, proj ε g = g := by
  apply DFunLike.coe_injective
  change (⇑(∑ ε : DirichletCharacter ℂ N, proj ε g) : ℍ → ℂ) = ⇑g
  rw [coe_sum]
  simp_rw [coe_proj]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hφ : ((N.totient : ℂ)) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos N)).ne'

  have horth : ∀ u : (ZMod N)ˣ,
      ∑ ε : DirichletCharacter ℂ N, ε ((u⁻¹ : (ZMod N)ˣ) : ZMod N)
        = if u = 1 then (N.totient : ℂ) else 0 := by
    intro u
    haveI : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
    have := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit u) 1
    simp only [map_one, mul_one, ZMod.inv_coe_unit, Units.val_eq_one] at this
    exact this
  simp_rw [← Finset.sum_smul, horth, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, smul_smul, inv_mul_cancel₀ hφ, one_smul]

  have h1 : lift (N := N) 1 ∈ Gamma1 N := by
    rw [mem_Gamma1_iff_dd (lift_mem 1), dd_lift, Units.val_one]
  exact slash_mem g h1

theorem mem_iSup_nebSpace (g : CuspForm Γ₁(N) k) :
    g ∈ ⨆ ε : DirichletCharacter ℂ N, nebSpace N k ε := by
  rw [← sum_proj g]
  exact Submodule.sum_mem _ fun ε _ => Submodule.mem_iSup_of_mem ε (proj_mem ε g)

end Diamond

section Periodicity

variable {k : ℤ} {p : ℕ}

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  simp [Gamma1_mem, ModularGroup.T]

theorem T_pow_mem_Gamma1 (N n : ℕ) : ModularGroup.T ^ n ∈ Gamma1 N :=
  pow_mem (T_mem_Gamma1 N) n

@[scoped simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

theorem heckeDiagMatrix_mul_T (hp : p ≠ 0) :
    heckeDiagMatrix p * (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ p) * heckeDiagMatrix p := by
  have hTp : ((ModularGroup.T ^ p : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (p : ℤ); 0, 1] := by
    rw [show ModularGroup.T ^ p = ModularGroup.T ^ (p : ℤ) from (zpow_natCast _ p).symm]
    exact ModularGroup.coe_T_zpow (p : ℤ)
  ext i j
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, mapGL_apply, mapGL_apply, mapGL_apply, mapGL_apply, hTp, ModularGroup.coe_T,
    val_heckeDiagMatrix hp]
  fin_cases i <;> fin_cases j <;> simp

theorem periodic_of_slash_T {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = F) :
    Periodic (F ∘ ofComplex) 1 := by
  have hT : ∀ τ : ℍ, F ((1 : ℝ) +ᵥ τ) = F τ := by
    intro τ
    have := congrFun h τ
    change (F ∣[k] ModularGroup.T) τ = F τ at this
    rw [SL_slash_apply] at this
    rw [← modular_T_smul]
    rw [← this]
    simp [denom, ModularGroup.T]
  intro w
  by_cases hw : 0 < w.im
  · have : 0 < (w + 1).im := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert hT ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have hw : w.im ≤ 0 := le_of_not_gt hw
    have : (w + 1).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

theorem slash_heckeDiagMatrix_slash_T (hp : p ≠ 0) {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ p)) = F) :
    (F ∣[k] heckeDiagMatrix p) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = F ∣[k] heckeDiagMatrix p := by
  rw [← SlashAction.slash_mul, heckeDiagMatrix_mul_T hp, SlashAction.slash_mul, h]

theorem isBoundedAtImInfty_slash_heckeDiagMatrix (hp : p ≠ 0) {F : ℍ → ℂ}
    (hF : IsBoundedAtImInfty F) : IsBoundedAtImInfty (F ∣[k] heckeDiagMatrix p) :=
  hF.slash k (by simp [val_heckeDiagMatrix hp])

theorem σ_heckeDiagMatrix_apply (p : ℕ) (c : ℂ) : UpperHalfPlane.σ (heckeDiagMatrix p) c = c := by
  rw [σ_heckeDiagMatrix]; rfl

end Periodicity

section Hecke

variable [NeZero N] {k : ℤ} {p : ℕ}

def heckeFun (k : ℤ) (ε : DirichletCharacter ℂ N) (p : ℕ) (F : ℍ → ℂ) : ℍ → ℂ :=
  heckeU k p F + ε (p : ZMod N) • (F ∣[k] heckeDiagMatrix p)

omit [NeZero N] in
theorem heckeFun_add (ε : DirichletCharacter ℂ N) (F G : ℍ → ℂ) :
    heckeFun k ε p (F + G) = heckeFun k ε p F + heckeFun k ε p G := by
  simp only [heckeFun, heckeU_add, SlashAction.add_slash, smul_add]
  abel

omit [NeZero N] in
theorem heckeFun_smul (ε : DirichletCharacter ℂ N) (c : ℂ) (F : ℍ → ℂ) :
    heckeFun k ε p (c • F) = c • heckeFun k ε p F := by
  simp only [heckeFun, heckeU_smul, ModularForm.smul_slash, σ_heckeDiagMatrix_apply, smul_add,
    smul_comm c]

def heckeForm (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N) (f : CuspForm Γ₁(N) k)
    (hf : CuspForm.HasNebentypus ε f) : CuspForm Γ₁(N) k where
  toFun := heckeFun k ε p ⇑f
  slash_action_eq' := by
    intro A hA
    obtain ⟨γ, hγ, rfl⟩ := hA
    have h := ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0 k hp hpN ε
      ((hasNebentypus_iff ε f).mp hf) γ (Gamma1_in_Gamma0 N hγ)
    change (heckeFun k ε p ⇑f) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = _
    rw [heckeFun, h, show ((γ 1 1 : ℤ) : ZMod N) = 1 from dd_eq_one_of_mem_Gamma1 hγ, map_one,
      one_smul]
  holo' := (ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k p).add
    (((CuspFormClass.holo f).slash k _).const_smul _)
  zero_at_cusps' := by
    intro c hc A hA
    have hU := CuspFormClass.isZeroAt_heckeU f p hc A hA
    have hT := CuspFormClass.isZeroAt_heckeT f p hc A hA
    have hD : IsZeroAtImInfty (((⇑f : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] A) := by
      have : (⇑f : ℍ → ℂ) ∣[k] heckeDiagMatrix p = heckeT k p ⇑f - heckeU k p ⇑f := by
        rw [heckeT_eq_heckeU_add]; abel
      rw [this, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash]
      exact hT.add hU.neg
    change IsZeroAtImInfty ((heckeFun k ε p ⇑f) ∣[k] A)
    rw [heckeFun, SlashAction.add_slash, ModularForm.smul_slash]
    exact hU.add (hD.smul _)

theorem coe_heckeForm (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm Γ₁(N) k) (hf : CuspForm.HasNebentypus ε f) :
    (⇑(heckeForm hp hpN ε f hf) : ℍ → ℂ) = heckeFun k ε p ⇑f := rfl

theorem heckeForm_mem (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm Γ₁(N) k) (hf : CuspForm.HasNebentypus ε f) :
    heckeForm hp hpN ε f hf ∈ nebSpace N k ε := by
  rw [mem_nebSpace, hasNebentypus_iff]
  intro γ hγ
  rw [coe_heckeForm]
  exact ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0 k hp hpN ε
    ((hasNebentypus_iff ε f).mp hf) γ hγ

def heckeLin (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N) :
    nebSpace N k ε →ₗ[ℂ] nebSpace N k ε where
  toFun f := ⟨heckeForm hp hpN ε f.1 f.2, heckeForm_mem hp hpN ε f.1 f.2⟩
  map_add' f g := by
    apply Subtype.ext
    apply DFunLike.coe_injective
    change heckeFun k ε p ⇑(f.1 + g.1) = heckeFun k ε p ⇑f.1 + heckeFun k ε p ⇑g.1
    rw [CuspForm.coe_add, heckeFun_add]
  map_smul' c f := by
    apply Subtype.ext
    apply DFunLike.coe_injective
    change heckeFun k ε p ⇑(c • f.1) = c • heckeFun k ε p ⇑f.1
    rw [CuspForm.IsGLPos.coe_smul, heckeFun_smul]

theorem coe_heckeLin (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : nebSpace N k ε) :
    (⇑((heckeLin hp hpN ε f : nebSpace N k ε) : CuspForm Γ₁(N) k) : ℍ → ℂ) = heckeFun k ε p ⇑(f : CuspForm Γ₁(N) k) :=
  rfl

structure Reg (F : ℍ → ℂ) : Prop where
  per : Periodic (F ∘ ofComplex) 1
  hol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F
  bdd : IsBoundedAtImInfty F

theorem reg_coe (g : CuspForm Γ₁(N) k) : Reg (⇑g : ℍ → ℂ) :=
  ⟨periodic_of_slash_T (slash_mem g (T_mem_Gamma1 N)), CuspFormClass.holo g,
    ModularFormClass.bdd_at_infty g⟩

theorem Reg.smul {F : ℍ → ℂ} (h : Reg F) (c : ℂ) : Reg (c • F) := by
  refine ⟨?_, h.hol.const_smul c, h.bdd.smul c⟩
  intro w
  have := h.per w
  simp only [comp_apply, Pi.smul_apply] at this ⊢
  rw [this]

theorem Reg.analyticAt {F : ℍ → ℂ} (h : Reg F) : AnalyticAt ℂ (cuspFunction 1 F) 0 :=
  analyticAt_cuspFunction_zero one_pos h.per h.hol h.bdd

theorem reg_slash_heckeDiagMatrix (hp : p ≠ 0) (g : CuspForm Γ₁(N) k) :
    Reg ((⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :=
  ⟨periodic_of_slash_T (slash_heckeDiagMatrix_slash_T hp (slash_mem g (T_pow_mem_Gamma1 N p))),
    (CuspFormClass.holo g).slash k _, isBoundedAtImInfty_slash_heckeDiagMatrix hp
      (ModularFormClass.bdd_at_infty g)⟩

theorem reg_heckeU (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm Γ₁(N) k) (hf : CuspForm.HasNebentypus ε f) : Reg (heckeU k p ⇑f) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hT : heckeFun k ε p ⇑f = heckeU k p ⇑f + ε (p : ZMod N) • ((⇑f : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :=
    rfl
  have hreg : Reg (heckeFun k ε p ⇑f) := reg_coe (heckeForm hp hpN ε f hf)
  have hD := reg_slash_heckeDiagMatrix hp0 f
  have hU : heckeU k p ⇑f = heckeFun k ε p ⇑f - ε (p : ZMod N) • ((⇑f : ℍ → ℂ) ∣[k] heckeDiagMatrix p) := by
    rw [hT, add_sub_cancel_right]
  refine ⟨?_, ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k p, ?_⟩
  · have hTinv : (heckeFun k ε p ⇑f) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) =
        heckeFun k ε p ⇑f := slash_mem (heckeForm hp hpN ε f hf) (T_mem_Gamma1 N)
    have hDinv := slash_heckeDiagMatrix_slash_T hp0 (slash_mem f (T_pow_mem_Gamma1 N p)) (k := k)
    apply periodic_of_slash_T (k := k)
    rw [hU, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, hTinv, ← sl_slash,
      ModularForm.SL_smul_slash, sl_slash, hDinv]
  · rw [hU]
    exact hreg.bdd.sub ((hD.bdd).smul _)

theorem qCoeff_heckeFun (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm Γ₁(N) k) (hf : CuspForm.HasNebentypus ε f) (n : ℕ) :
    ModularFormClass.qCoeff (heckeFun k ε p ⇑f) n
      = ModularFormClass.qCoeff (⇑f) (n * p)
        + ε (p : ZMod N) * (p : ℂ) ^ (k - 1)
          * (if p ∣ n then ModularFormClass.qCoeff (⇑f) (n / p) else 0) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hg := reg_coe f
  have hU := reg_heckeU hp hpN ε f hf
  have hD := reg_slash_heckeDiagMatrix hp0 f

  set D : ℍ → ℂ := (⇑f : ℍ → ℂ) ∣[k] heckeDiagMatrix p with hDdef
  set G : ℍ → ℂ := fun τ => f (heckeDiagMatrix p • τ) with hG
  have hDG : D = ((p : ℂ) ^ (k - 1)) • G := by
    funext τ
    rw [hDdef, slash_heckeDiagMatrix_apply k hp0, Pi.smul_apply, smul_eq_mul]
  have hpk : ((p : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp0)
  have hGD : G = ((p : ℂ) ^ (k - 1))⁻¹ • D := by
    rw [hDG, smul_smul, inv_mul_cancel₀ hpk, one_smul]
  have hGreg : Reg G := by rw [hGD]; exact hD.smul _
  have hqD : ModularFormClass.qCoeff D n
      = (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff (⇑f) (n / p) else 0) := by
    rw [ModularFormClass.qCoeff, hDG, qExpansion_smul hGreg.analyticAt, map_smul, smul_eq_mul]
    congr 1
    exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul hg.per hg.hol hg.bdd hp0 n
  have hqU : ModularFormClass.qCoeff (heckeU k p ⇑f) n = ModularFormClass.qCoeff (⇑f) (n * p) := by
    rw [UpperHalfPlane.qCoeff_heckeU hg.per hg.hol hg.bdd k hp0 n, coeffHeckeU_apply]
  rw [heckeFun, ModularFormClass.qCoeff, qExpansion_add hU.analyticAt (hD.smul _).analyticAt,
    qExpansion_smul hD.analyticAt, map_add, map_smul, smul_eq_mul]
  change ModularFormClass.qCoeff (heckeU k p ⇑f) n + ε (p : ZMod N) * ModularFormClass.qCoeff D n = _
  rw [hqU, hqD, mul_assoc]

def cT (e : ℂ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + e * (if p ∣ n then a (n / p) else 0)

omit [NeZero N] in

theorem cT_cT {p q : ℕ} (hp : 0 < p) (hcop : Nat.Coprime p q) (e e' : ℂ) (a : ℕ → ℂ)
    (n : ℕ) :
    cT e p (cT e' q a) n
      = a (n * (p * q)) + e' * (if q ∣ n then a (n / q * p) else 0)
        + e * (if p ∣ n then a (n / p * q) else 0)
        + e * e' * (if p * q ∣ n then a (n / (p * q)) else 0) := by
  simp only [cT]
  have hqnp : (q ∣ n * p) ↔ q ∣ n :=
    ⟨fun h => Nat.Coprime.dvd_of_dvd_mul_right hcop.symm h, fun h => dvd_mul_of_dvd_left h p⟩
  have h2 : (if q ∣ n * p then a (n * p / q) else 0) = (if q ∣ n then a (n / q * p) else 0) := by
    by_cases hqn : q ∣ n
    · rw [if_pos (hqnp.mpr hqn), if_pos hqn, Nat.mul_div_right_comm hqn]
    · rw [if_neg (fun h => hqn (hqnp.mp h)), if_neg hqn]
  have h4 : (if p ∣ n then (a (n / p * q) + e' * (if q ∣ n / p then a (n / p / q) else 0)) else 0)
      = (if p ∣ n then a (n / p * q) else 0)
        + e' * (if p * q ∣ n then a (n / (p * q)) else 0) := by
    by_cases hpn : p ∣ n
    · rw [if_pos hpn, if_pos hpn, Nat.div_div_eq_div_mul]
      obtain ⟨m, rfl⟩ := hpn
      have hiff : q ∣ p * m / p ↔ p * q ∣ p * m := by
        rw [Nat.mul_div_cancel_left _ hp]
        exact (Nat.mul_dvd_mul_iff_left hp).symm
      by_cases hqm : q ∣ p * m / p
      · rw [if_pos hqm, if_pos (hiff.mp hqm)]
      · rw [if_neg hqm, if_neg (fun h => hqm (hiff.mpr h))]
    · rw [if_neg hpn, if_neg hpn, if_neg (fun h => hpn (dvd_trans (dvd_mul_right p q) h))]
      ring
  rw [h2, h4, mul_assoc n p q]
  ring

omit [NeZero N] in
theorem cT_comm {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (e e' : ℂ) (a : ℕ → ℂ)
    (n : ℕ) : cT e p (cT e' q a) n = cT e' q (cT e p a) n := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [cT_cT hp.pos hcop, cT_cT hq.pos hcop.symm, mul_comm q p, mul_comm e' e]
  ring

theorem qCoeff_heckeFun' (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm Γ₁(N) k) (hf : CuspForm.HasNebentypus ε f) :
    ModularFormClass.qCoeff (heckeFun k ε p ⇑f)
      = cT (ε (p : ZMod N) * (p : ℂ) ^ (k - 1)) p (ModularFormClass.qCoeff (⇑f)) := by
  funext n
  rw [qCoeff_heckeFun hp hpN ε f hf n, cT]

theorem heckeLin_comm {q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (ε : DirichletCharacter ℂ N) :
    Commute (heckeLin (k := k) hp hpN ε) (heckeLin hq hqN ε) := by
  rcases eq_or_ne p q with rfl | hpq
  · exact Commute.refl _
  refine LinearMap.ext fun f => ?_
  apply Subtype.ext
  apply DFunLike.coe_injective
  change heckeFun k ε p ⇑((heckeLin hq hqN ε f : nebSpace N k ε) : CuspForm Γ₁(N) k)
    = heckeFun k ε q ⇑((heckeLin hp hpN ε f : nebSpace N k ε) : CuspForm Γ₁(N) k)
  set g₁ : CuspForm Γ₁(N) k := ((heckeLin hq hqN ε f : nebSpace N k ε) : CuspForm Γ₁(N) k)
  set g₂ : CuspForm Γ₁(N) k := ((heckeLin hp hpN ε f : nebSpace N k ε) : CuspForm Γ₁(N) k)
  have hg₁ : CuspForm.HasNebentypus ε g₁ := (heckeLin hq hqN ε f).2
  have hg₂ : CuspForm.HasNebentypus ε g₂ := (heckeLin hp hpN ε f).2
  have r₁ : Reg (heckeFun k ε p ⇑g₁) := reg_coe (heckeForm hp hpN ε g₁ hg₁)
  have r₂ : Reg (heckeFun k ε q ⇑g₂) := reg_coe (heckeForm hq hqN ε g₂ hg₂)
  refine UpperHalfPlane.eq_of_forall_qCoeff_eq r₁.per r₁.hol r₁.bdd r₂.per r₂.hol r₂.bdd fun n => ?_
  rw [qCoeff_heckeFun' hp hpN ε g₁ hg₁, qCoeff_heckeFun' hq hqN ε g₂ hg₂]
  change cT _ p (ModularFormClass.qCoeff (heckeFun k ε q ⇑(f : CuspForm Γ₁(N) k))) n
    = cT _ q (ModularFormClass.qCoeff (heckeFun k ε p ⇑(f : CuspForm Γ₁(N) k))) n
  rw [qCoeff_heckeFun' hq hqN ε _ f.2, qCoeff_heckeFun' hp hpN ε _ f.2]
  exact cT_comm hp hq hpq _ _ _ n

end Hecke

section Petersson

variable [NeZero N] {k : ℤ}

def B (ε : DirichletCharacter ℂ N) (f g : nebSpace N k ε) : ℂ :=
  CuspForm.peterssonOn (Gamma1 N) k ⇑(f : CuspForm Γ₁(N) k) ⇑(g : CuspForm Γ₁(N) k)

theorem isPosDefHerm_B (ε : DirichletCharacter ℂ N) : SimulEigen.IsPosDefHerm (B (k := k) ε) where
  add_right f g h := by
    have := (CuspForm.peterssonOn_add_smul_conj (Gamma1 N) k (f : CuspForm Γ₁(N) k)
      (g : CuspForm Γ₁(N) k) (h : CuspForm Γ₁(N) k) 0).1
    exact this
  smul_right f c g := by
    have := (CuspForm.peterssonOn_add_smul_conj (Gamma1 N) k (f : CuspForm Γ₁(N) k)
      (g : CuspForm Γ₁(N) k) (g : CuspForm Γ₁(N) k) c).2.1
    exact this
  conj_symm f g :=
    (CuspForm.peterssonOn_add_smul_conj (Gamma1 N) k (f : CuspForm Γ₁(N) k)
      (g : CuspForm Γ₁(N) k) (g : CuspForm Γ₁(N) k) 0).2.2
  definite f hf := by
    have := (CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff (Gamma1 N) k
      (f : CuspForm Γ₁(N) k)).2.2.mp hf
    exact Subtype.ext this

def GoodPrime (N : ℕ) : Type := {p : ℕ // p.Prime ∧ ¬ p ∣ N}

omit [NeZero N] in
theorem norm_char_prime (ε : DirichletCharacter ℂ N) (i : GoodPrime N) :
    ‖ε ((i.1 : ℕ) : ZMod N)‖ = 1 := by
  have hu : IsUnit ((i.1 : ℕ) : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd i.2.1).mpr i.2.2
  have := ε.unit_norm_eq_one hu.unit
  rwa [IsUnit.unit_spec] at this

def croot (ε : DirichletCharacter ℂ N) (i : GoodPrime N) : ℂ :=
  (IsAlgClosed.exists_pow_nat_eq (conj (ε ((i.1 : ℕ) : ZMod N))) two_pos).choose

omit [NeZero N] in
theorem croot_sq (ε : DirichletCharacter ℂ N) (i : GoodPrime N) :
    croot ε i ^ 2 = conj (ε ((i.1 : ℕ) : ZMod N)) :=
  (IsAlgClosed.exists_pow_nat_eq (conj (ε ((i.1 : ℕ) : ZMod N))) two_pos).choose_spec

omit [NeZero N] in
theorem norm_croot (ε : DirichletCharacter ℂ N) (i : GoodPrime N) : ‖croot ε i‖ = 1 := by
  have h : ‖croot ε i‖ ^ 2 = 1 := by
    rw [← norm_pow, croot_sq, Complex.norm_conj, norm_char_prime]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

omit [NeZero N] in
theorem croot_ne_zero (ε : DirichletCharacter ℂ N) (i : GoodPrime N) : croot ε i ≠ 0 := by
  intro h; have := norm_croot ε i; rw [h, norm_zero] at this; exact zero_ne_one this

omit [NeZero N] in
theorem conj_croot_mul (ε : DirichletCharacter ℂ N) (i : GoodPrime N) :
    conj (croot ε i) * conj (ε ((i.1 : ℕ) : ZMod N)) = croot ε i := by
  rw [← Complex.inv_eq_conj (norm_croot ε i), ← croot_sq, sq, ← mul_assoc,
    inv_mul_cancel₀ (croot_ne_zero ε i), one_mul]

def heckeFamily (ε : DirichletCharacter ℂ N) (i : GoodPrime N) : nebSpace N k ε →ₗ[ℂ] nebSpace N k ε :=
  croot ε i • heckeLin i.2.1 i.2.2 ε

theorem heckeFamily_comm (ε : DirichletCharacter ℂ N) (i j : GoodPrime N) :
    Commute (heckeFamily (k := k) ε i) (heckeFamily ε j) :=
  ((heckeLin_comm i.2.1 i.2.2 j.2.1 j.2.2 ε).smul_left _).smul_right _

theorem heckeFamily_selfAdjoint (ε : DirichletCharacter ℂ N) (i : GoodPrime N) (f g : nebSpace N k ε) :
    B ε (heckeFamily ε i f) g = B ε f (heckeFamily ε i g) := by
  have hB := isPosDefHerm_B (k := k) ε
  have hadj : B ε (heckeLin i.2.1 i.2.2 ε f) g
      = conj (ε ((i.1 : ℕ) : ZMod N)) * B ε f (heckeLin i.2.1 i.2.2 ε g) :=
    CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus N k ε i.2.1 i.2.2
      (f : CuspForm Γ₁(N) k) (g : CuspForm Γ₁(N) k) f.2 g.2
  rw [heckeFamily, LinearMap.smul_apply, LinearMap.smul_apply, hB.smul_left, hB.smul_right, hadj,
    ← mul_assoc, conj_croot_mul]

theorem span_eigen_eq_top (ε : DirichletCharacter ℂ N) :
    Submodule.span ℂ {v : nebSpace N k ε | ∀ i : GoodPrime N, ∃ c : ℂ, heckeFamily ε i v = c • v} = ⊤ := by
  haveI : FiniteDimensional ℂ (CuspForm Γ₁(N) k) := CuspForm.finiteDimensional_of_isArithmetic _ k
  exact (isPosDefHerm_B (k := k) ε).span_common_eigen (heckeFamily ε) (heckeFamily_comm ε)
    (heckeFamily_selfAdjoint ε)

end Petersson

section Assembly

variable [NeZero N] {k : ℤ}

def eigenSet (N : ℕ) [NeZero N] (k : ℤ) : Set (CuspForm Γ₁(N) k) :=
  {v | ∃ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε v ∧
    ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ lam : ℂ, ∀ m : ℕ,
      ModularFormClass.qCoeff v (p * m) +
          ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
            (if p ∣ m then ModularFormClass.qCoeff v (m / p) else 0) =
        lam * ModularFormClass.qCoeff v m}

theorem mem_eigenSet_of_eigen (ε : DirichletCharacter ℂ N) (v : nebSpace N k ε)
    (hv : ∀ i : GoodPrime N, ∃ c : ℂ, heckeFamily ε i v = c • v) :
    (v : CuspForm Γ₁(N) k) ∈ eigenSet N k := by
  refine ⟨ε, v.2, fun p hp hpN => ?_⟩
  obtain ⟨c, hc⟩ := hv ⟨p, hp, hpN⟩
  set lam : ℂ := (croot ε ⟨p, hp, hpN⟩)⁻¹ * c with hlam
  have hL : heckeLin hp hpN ε v = lam • v := by
    have h1 : croot ε ⟨p, hp, hpN⟩ • heckeLin hp hpN ε v = c • v := hc
    have := congrArg (fun w => (croot ε ⟨p, hp, hpN⟩)⁻¹ • w) h1
    simp only [smul_smul, inv_mul_cancel₀ (croot_ne_zero ε _), one_smul] at this
    rw [this, hlam]
  have hfun : heckeFun k ε p ⇑(v : CuspForm Γ₁(N) k) = lam • ⇑(v : CuspForm Γ₁(N) k) := by
    have := congrArg (fun w : nebSpace N k ε => (⇑(w : CuspForm Γ₁(N) k) : ℍ → ℂ)) hL
    simp only [Submodule.coe_smul, CuspForm.IsGLPos.coe_smul] at this
    exact this
  refine ⟨lam, fun m => ?_⟩
  have hq := congrArg (fun F : ℍ → ℂ => ModularFormClass.qCoeff F m) hfun
  have hsm : ModularFormClass.qCoeff (lam • ⇑(v : CuspForm Γ₁(N) k)) m
      = lam * ModularFormClass.qCoeff (⇑(v : CuspForm Γ₁(N) k)) m := by
    rw [ModularFormClass.qCoeff, ModularFormClass.qCoeff,
      qExpansion_smul (reg_coe (v : CuspForm Γ₁(N) k)).analyticAt, map_smul, smul_eq_mul]
  rw [qCoeff_heckeFun hp hpN ε _ v.2 m, hsm] at hq
  rw [mul_comm p m]
  exact hq

theorem nebSpace_le_span (ε : DirichletCharacter ℂ N) :
    (nebSpace N k ε : Submodule ℂ (CuspForm Γ₁(N) k)) ≤ Submodule.span ℂ (eigenSet N k) := by
  intro g hg
  have hmem : (⟨g, hg⟩ : nebSpace N k ε) ∈
      Submodule.span ℂ {v : nebSpace N k ε | ∀ i : GoodPrime N, ∃ c : ℂ, heckeFamily ε i v = c • v} := by
    rw [span_eigen_eq_top]; trivial
  have himg := Submodule.mem_map_of_mem (f := (nebSpace N k ε).subtype) hmem
  rw [Submodule.map_span] at himg
  refine Submodule.span_mono ?_ himg
  rintro _ ⟨v, hv, rfl⟩
  exact mem_eigenSet_of_eigen ε v hv

theorem span_eigenSet_eq_top : Submodule.span ℂ (eigenSet N k) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have := mem_iSup_nebSpace (k := k) g
  exact (iSup_le fun ε => nebSpace_le_span (k := k) ε) this

theorem main (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm Γ₁(N) k)),
      ∀ i, ∃ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε (b i) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ lam : ℂ, ∀ m : ℕ,
          ModularFormClass.qCoeff (b i) (p * m) +
              ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
                (if p ∣ m then ModularFormClass.qCoeff (b i) (m / p) else 0) =
            lam * ModularFormClass.qCoeff (b i) m := by
  haveI : FiniteDimensional ℂ (CuspForm Γ₁(N) k) := CuspForm.finiteDimensional_of_isArithmetic _ k
  obtain ⟨t, ht, hspan, hli⟩ := exists_linearIndependent ℂ (eigenSet N k)
  have hfin : t.Finite := hli.setFinite
  letI : Fintype t := hfin.fintype
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : t → CuspForm Γ₁(N) k)) := by
    rw [Subtype.range_coe, hspan, span_eigenSet_eq_top]
  let b₀ : Module.Basis t ℂ (CuspForm Γ₁(N) k) := Module.Basis.mk hli htop
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  refine ⟨Fintype.card t, b₀.reindex e, fun i => ?_⟩
  have hbi : (b₀.reindex e) i = ((e.symm i : t) : CuspForm Γ₁(N) k) := by
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
  have hmem : (b₀.reindex e) i ∈ eigenSet N k := by
    rw [hbi]; exact ht (e.symm i).2
  exact hmem

end Assembly

end SSbasis
p2m_reactivate "P2MW.S_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen.SSbasis"

end
p2m_reactivate "P2MW.S_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen.SSbasis"

theorem solution
    (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ i, ∃ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε (b i) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ lam : ℂ, ∀ m : ℕ,
          ModularFormClass.qCoeff (b i) (p * m) +
              ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
                (if p ∣ m then ModularFormClass.qCoeff (b i) (m / p) else 0) =
            lam * ModularFormClass.qCoeff (b i) m :=
  SSbasis.main N k

end S_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen
end P2MW
export P2MW.S_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen (solution)
