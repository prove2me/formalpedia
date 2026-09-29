-- Prove2me | solution 1 for CuspForm.exists_hasNebentypus_qCoeff_hecke_eigen_forall_of_qCoeff_hecke_eigen_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/cd7beef8-185f-58c0-9e80-a6123b2de537

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_ModularForm_heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeT
import Theorems.Thm_UpperHalfPlane_qCoeff_heckeU
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_hasNebentypus_qCoeff_hecke_eigen_forall_of_qCoeff_hecke_eigen_of_not_mem

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularForm UpperHalfPlane Filter Function
open scoped ModularForm UpperHalfPlane MatrixGroups ComplexConjugate

namespace RefineEigenformG3a

variable {N : ℕ}

private theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

private theorem det_mod (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hγ
  have := congrArg (Int.cast : ℤ → ZMod N) (det_eq γ)
  push_cast at this
  rw [hc] at this
  linear_combination this

private def dd (γ : SL(2, ℤ)) : ZMod N := ((γ 1 1 : ℤ) : ZMod N)

private theorem dd_mul {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 N) (h₂ : γ₂ ∈ Gamma0 N) :
    dd (N := N) (γ₁ * γ₂) = dd (N := N) γ₁ * dd γ₂ := by
  have := map_mul (Gamma0Map N) ⟨γ₁, h₁⟩ ⟨γ₂, h₂⟩
  exact this

private theorem dd_one : dd (N := N) 1 = 1 := by simp [dd]

private theorem isUnit_dd {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) : IsUnit (dd (N := N) γ) :=
  IsUnit.of_mul_eq_one _ (by rw [dd, mul_comm]; exact det_mod γ hγ)

private theorem mem_Gamma1_iff_dd {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    γ ∈ Gamma1 N ↔ dd (N := N) γ = 1 := by
  rw [Gamma1_mem, dd]
  constructor
  · rintro ⟨-, h, -⟩; simpa using h
  · intro hd
    have ha : ((γ 0 0 : ℤ) : ZMod N) = 1 := by
      have := det_mod γ hγ; rw [hd, mul_one] at this; exact this
    exact ⟨by simpa using ha, by simpa using hd, by simpa using Gamma0_mem.mp hγ⟩

private theorem dd_eq_one_of_mem_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) : dd (N := N) γ = 1 :=
  (mem_Gamma1_iff_dd (Gamma1_in_Gamma0 N hγ)).mp hγ

section Slash

variable {k : ℤ}

private theorem sl_slash (f : ℍ → ℂ) (γ : SL(2, ℤ)) :
    f ∣[k] γ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) := rfl

private theorem slash_mem (g : CuspForm (Gamma1 N) k) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) :
    (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑g :=
  SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)

private theorem hasNebentypus_iff (ε : DirichletCharacter ℂ N) (g : CuspForm (Gamma1 N) k) :
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

end Slash

section NebSpace

variable [NeZero N] {k : ℤ}

private def nebSpace (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) :
    Submodule ℂ (CuspForm (Gamma1 N) k) where
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

private theorem mem_nebSpace {ε : DirichletCharacter ℂ N} {g : CuspForm (Gamma1 N) k} :
    g ∈ nebSpace N k ε ↔ CuspForm.HasNebentypus ε g := Iff.rfl

end NebSpace

section Periodicity

variable {k : ℤ} {p : ℕ}

private theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  simp [Gamma1_mem, ModularGroup.T]

private theorem T_pow_mem_Gamma1 (N n : ℕ) : ModularGroup.T ^ n ∈ Gamma1 N :=
  pow_mem (T_mem_Gamma1 N) n

@[local simp] private theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

private theorem heckeDiagMatrix_mul_T (hp : p ≠ 0) :
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

private theorem periodic_of_slash_T {F : ℍ → ℂ}
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

private theorem slash_heckeDiagMatrix_slash_T (hp : p ≠ 0) {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ p)) = F) :
    (F ∣[k] heckeDiagMatrix p) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = F ∣[k] heckeDiagMatrix p := by
  rw [← SlashAction.slash_mul, heckeDiagMatrix_mul_T hp, SlashAction.slash_mul, h]

private theorem isBoundedAtImInfty_slash_heckeDiagMatrix (hp : p ≠ 0) {F : ℍ → ℂ}
    (hF : IsBoundedAtImInfty F) : IsBoundedAtImInfty (F ∣[k] heckeDiagMatrix p) :=
  hF.slash k (by simp [val_heckeDiagMatrix hp])

private theorem σ_heckeDiagMatrix_apply (p : ℕ) (c : ℂ) : UpperHalfPlane.σ (heckeDiagMatrix p) c = c := by
  rw [σ_heckeDiagMatrix]; rfl

end Periodicity

section Hecke

variable [NeZero N] {k : ℤ} {p : ℕ}

private def heckeFun (k : ℤ) (ε : DirichletCharacter ℂ N) (p : ℕ) (F : ℍ → ℂ) : ℍ → ℂ :=
  heckeU k p F + ε (p : ZMod N) • (F ∣[k] heckeDiagMatrix p)

omit [NeZero N] in
private theorem heckeFun_add (ε : DirichletCharacter ℂ N) (F G : ℍ → ℂ) :
    heckeFun k ε p (F + G) = heckeFun k ε p F + heckeFun k ε p G := by
  simp only [heckeFun, heckeU_add, SlashAction.add_slash, smul_add]
  abel

omit [NeZero N] in
private theorem heckeFun_smul (ε : DirichletCharacter ℂ N) (c : ℂ) (F : ℍ → ℂ) :
    heckeFun k ε p (c • F) = c • heckeFun k ε p F := by
  simp only [heckeFun, heckeU_smul, ModularForm.smul_slash, σ_heckeDiagMatrix_apply, smul_add,
    smul_comm c]

private def heckeForm (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) k)
    (hf : CuspForm.HasNebentypus ε f) : CuspForm (Gamma1 N) k where
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

private theorem coe_heckeForm (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) k) (hf : CuspForm.HasNebentypus ε f) :
    (⇑(heckeForm hp hpN ε f hf) : ℍ → ℂ) = heckeFun k ε p ⇑f := rfl

private theorem heckeForm_mem (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) k) (hf : CuspForm.HasNebentypus ε f) :
    heckeForm hp hpN ε f hf ∈ nebSpace N k ε := by
  rw [mem_nebSpace, hasNebentypus_iff]
  intro γ hγ
  rw [coe_heckeForm]
  exact ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0 k hp hpN ε
    ((hasNebentypus_iff ε f).mp hf) γ hγ

private def heckeLin (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N) :
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

private theorem coe_heckeLin (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : nebSpace N k ε) :
    (⇑((heckeLin hp hpN ε f : nebSpace N k ε) : CuspForm (Gamma1 N) k) : ℍ → ℂ) = heckeFun k ε p ⇑(f : CuspForm (Gamma1 N) k) :=
  rfl

private structure Reg (F : ℍ → ℂ) : Prop where
  per : Periodic (F ∘ ofComplex) 1
  hol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F
  bdd : IsBoundedAtImInfty F

private theorem reg_coe (g : CuspForm (Gamma1 N) k) : Reg (⇑g : ℍ → ℂ) :=
  ⟨periodic_of_slash_T (slash_mem g (T_mem_Gamma1 N)), CuspFormClass.holo g,
    ModularFormClass.bdd_at_infty g⟩

private theorem Reg.smul {F : ℍ → ℂ} (h : Reg F) (c : ℂ) : Reg (c • F) := by
  refine ⟨?_, h.hol.const_smul c, h.bdd.smul c⟩
  intro w
  have := h.per w
  simp only [comp_apply, Pi.smul_apply] at this ⊢
  rw [this]

private theorem Reg.analyticAt {F : ℍ → ℂ} (h : Reg F) : AnalyticAt ℂ (cuspFunction 1 F) 0 :=
  analyticAt_cuspFunction_zero one_pos h.per h.hol h.bdd

private theorem reg_slash_heckeDiagMatrix (hp : p ≠ 0) (g : CuspForm (Gamma1 N) k) :
    Reg ((⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :=
  ⟨periodic_of_slash_T (slash_heckeDiagMatrix_slash_T hp (slash_mem g (T_pow_mem_Gamma1 N p))),
    (CuspFormClass.holo g).slash k _, isBoundedAtImInfty_slash_heckeDiagMatrix hp
      (ModularFormClass.bdd_at_infty g)⟩

private theorem reg_heckeU (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) k) (hf : CuspForm.HasNebentypus ε f) : Reg (heckeU k p ⇑f) := by
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

private theorem qCoeff_heckeFun (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) k) (hf : CuspForm.HasNebentypus ε f) (n : ℕ) :
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

private def cT (e : ℂ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + e * (if p ∣ n then a (n / p) else 0)

omit [NeZero N] in

private theorem cT_cT {p q : ℕ} (hp : 0 < p) (hcop : Nat.Coprime p q) (e e' : ℂ) (a : ℕ → ℂ)
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
private theorem cT_comm {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (e e' : ℂ) (a : ℕ → ℂ)
    (n : ℕ) : cT e p (cT e' q a) n = cT e' q (cT e p a) n := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [cT_cT hp.pos hcop, cT_cT hq.pos hcop.symm, mul_comm q p, mul_comm e' e]
  ring

private theorem qCoeff_heckeFun' (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) k) (hf : CuspForm.HasNebentypus ε f) :
    ModularFormClass.qCoeff (heckeFun k ε p ⇑f)
      = cT (ε (p : ZMod N) * (p : ℂ) ^ (k - 1)) p (ModularFormClass.qCoeff (⇑f)) := by
  funext n
  rw [qCoeff_heckeFun hp hpN ε f hf n, cT]

private theorem heckeLin_comm {q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (ε : DirichletCharacter ℂ N) :
    Commute (heckeLin (k := k) hp hpN ε) (heckeLin hq hqN ε) := by
  rcases eq_or_ne p q with rfl | hpq
  · exact Commute.refl _
  refine LinearMap.ext fun f => ?_
  apply Subtype.ext
  apply DFunLike.coe_injective
  change heckeFun k ε p ⇑((heckeLin hq hqN ε f : nebSpace N k ε) : CuspForm (Gamma1 N) k)
    = heckeFun k ε q ⇑((heckeLin hp hpN ε f : nebSpace N k ε) : CuspForm (Gamma1 N) k)
  set g₁ : CuspForm (Gamma1 N) k := ((heckeLin hq hqN ε f : nebSpace N k ε) : CuspForm (Gamma1 N) k)
  set g₂ : CuspForm (Gamma1 N) k := ((heckeLin hp hpN ε f : nebSpace N k ε) : CuspForm (Gamma1 N) k)
  have hg₁ : CuspForm.HasNebentypus ε g₁ := (heckeLin hq hqN ε f).2
  have hg₂ : CuspForm.HasNebentypus ε g₂ := (heckeLin hp hpN ε f).2
  have r₁ : Reg (heckeFun k ε p ⇑g₁) := reg_coe (heckeForm hp hpN ε g₁ hg₁)
  have r₂ : Reg (heckeFun k ε q ⇑g₂) := reg_coe (heckeForm hq hqN ε g₂ hg₂)
  refine UpperHalfPlane.eq_of_forall_qCoeff_eq r₁.per r₁.hol r₁.bdd r₂.per r₂.hol r₂.bdd fun n => ?_
  rw [qCoeff_heckeFun' hp hpN ε g₁ hg₁, qCoeff_heckeFun' hq hqN ε g₂ hg₂]
  change cT _ p (ModularFormClass.qCoeff (heckeFun k ε q ⇑(f : CuspForm (Gamma1 N) k))) n
    = cT _ q (ModularFormClass.qCoeff (heckeFun k ε p ⇑(f : CuspForm (Gamma1 N) k))) n
  rw [qCoeff_heckeFun' hq hqN ε _ f.2, qCoeff_heckeFun' hp hpN ε _ f.2]
  exact cT_comm hp hq hpq _ _ _ n

end Hecke

section HeckeU

variable [NeZero N] {k : ℤ} {q : ℕ}

private def uForm (hq : q ∣ N) (f : CuspForm (Gamma1 N) k) : CuspForm (Gamma1 N) k :=
  (CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd k hq f).choose

private theorem coe_uForm (hq : q ∣ N) (f : CuspForm (Gamma1 N) k) :
    (⇑(uForm hq f) : ℍ → ℂ) = heckeU k q ⇑f :=
  (CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd k hq f).choose_spec.1

private theorem hasNebentypus_uForm (hq : q ∣ N) (f : CuspForm (Gamma1 N) k)
    (ε : DirichletCharacter ℂ N) (hf : CuspForm.HasNebentypus ε f) :
    CuspForm.HasNebentypus ε (uForm hq f) :=
  (CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd k hq f).choose_spec.2.2 ε hf

private def uLin (hq : q ∣ N) (ε : DirichletCharacter ℂ N) :
    nebSpace N k ε →ₗ[ℂ] nebSpace N k ε where
  toFun f := ⟨uForm hq f.1, hasNebentypus_uForm hq f.1 ε f.2⟩
  map_add' f g := by
    apply Subtype.ext
    apply DFunLike.coe_injective
    change (⇑(uForm hq (f.1 + g.1)) : ℍ → ℂ) = ⇑(uForm hq f.1 + uForm hq g.1)
    rw [CuspForm.coe_add, coe_uForm, coe_uForm, coe_uForm, CuspForm.coe_add, heckeU_add]
  map_smul' c f := by
    apply Subtype.ext
    apply DFunLike.coe_injective
    change (⇑(uForm hq (c • f.1)) : ℍ → ℂ) = ⇑(c • uForm hq f.1)
    rw [CuspForm.IsGLPos.coe_smul, coe_uForm, coe_uForm, CuspForm.IsGLPos.coe_smul, heckeU_smul]

private theorem coe_uLin (hq : q ∣ N) (ε : DirichletCharacter ℂ N) (f : nebSpace N k ε) :
    (⇑((uLin hq ε f : nebSpace N k ε) : CuspForm (Gamma1 N) k) : ℍ → ℂ)
      = heckeU k q ⇑(f : CuspForm (Gamma1 N) k) :=
  coe_uForm hq f.1

private theorem qCoeff_heckeU_coe (hq0 : q ≠ 0) (g : CuspForm (Gamma1 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (heckeU k q ⇑g) n = ModularFormClass.qCoeff (⇑g) (n * q) := by
  have hg := reg_coe g
  rw [UpperHalfPlane.qCoeff_heckeU hg.per hg.hol hg.bdd k hq0 n, coeffHeckeU_apply]

private theorem reg_heckeU_of_dvd (hq : q ∣ N) (g : CuspForm (Gamma1 N) k) : Reg (heckeU k q ⇑g) := by
  rw [← coe_uForm hq g]
  exact reg_coe _

private theorem qCoeff_smul_coe (c : ℂ) (g : CuspForm (Gamma1 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (c • (⇑g : ℍ → ℂ)) n = c * ModularFormClass.qCoeff (⇑g) n := by
  rw [ModularFormClass.qCoeff, ModularFormClass.qCoeff, qExpansion_smul (reg_coe g).analyticAt,
    map_smul, smul_eq_mul]

private theorem uLin_comm {q' : ℕ} (hq : q.Prime) (hqN : q ∣ N) (hq' : q'.Prime) (hq'N : q' ∣ N)
    (ε : DirichletCharacter ℂ N) :
    Commute (uLin (k := k) hqN ε) (uLin hq'N ε) := by
  refine LinearMap.ext fun f => ?_
  apply Subtype.ext
  apply DFunLike.coe_injective
  change (⇑((uLin hqN ε (uLin hq'N ε f) : nebSpace N k ε) : CuspForm (Gamma1 N) k) : ℍ → ℂ)
    = ⇑((uLin hq'N ε (uLin hqN ε f) : nebSpace N k ε) : CuspForm (Gamma1 N) k)
  rw [coe_uLin hqN ε (uLin hq'N ε f), coe_uLin hq'N ε (uLin hqN ε f)]
  have r₁ := reg_heckeU_of_dvd (k := k) hqN ((uLin hq'N ε f : nebSpace N k ε) : CuspForm (Gamma1 N) k)
  have r₂ := reg_heckeU_of_dvd (k := k) hq'N ((uLin hqN ε f : nebSpace N k ε) : CuspForm (Gamma1 N) k)
  refine UpperHalfPlane.eq_of_forall_qCoeff_eq r₁.per r₁.hol r₁.bdd r₂.per r₂.hol r₂.bdd fun n => ?_
  rw [qCoeff_heckeU_coe hq.ne_zero, qCoeff_heckeU_coe hq'.ne_zero, coe_uLin, coe_uLin,
    qCoeff_heckeU_coe hq'.ne_zero, qCoeff_heckeU_coe hq.ne_zero, mul_right_comm]

private theorem heckeLin_uLin_comm {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hq : q.Prime) (hqN : q ∣ N)
    (ε : DirichletCharacter ℂ N) :
    Commute (heckeLin (k := k) hp hpN ε) (uLin hqN ε) := by
  have hpq : Nat.Coprime p q := by
    rw [Nat.coprime_primes hp hq]
    rintro rfl
    exact hpN hqN
  refine LinearMap.ext fun f => ?_
  apply Subtype.ext
  apply DFunLike.coe_injective
  change heckeFun k ε p ⇑((uLin hqN ε f : nebSpace N k ε) : CuspForm (Gamma1 N) k)
    = (⇑((uLin hqN ε (heckeLin hp hpN ε f) : nebSpace N k ε) : CuspForm (Gamma1 N) k) : ℍ → ℂ)
  rw [coe_uLin hqN ε (heckeLin hp hpN ε f)]
  have hg₁ : CuspForm.HasNebentypus ε ((uLin hqN ε f : nebSpace N k ε) : CuspForm (Gamma1 N) k) :=
    (uLin hqN ε f).2
  have r₁ : Reg (heckeFun k ε p ⇑((uLin hqN ε f : nebSpace N k ε) : CuspForm (Gamma1 N) k)) :=
    reg_coe (heckeForm hp hpN ε _ hg₁)
  have r₂ := reg_heckeU_of_dvd (k := k) hqN ((heckeLin hp hpN ε f : nebSpace N k ε) : CuspForm (Gamma1 N) k)
  refine UpperHalfPlane.eq_of_forall_qCoeff_eq r₁.per r₁.hol r₁.bdd r₂.per r₂.hol r₂.bdd fun n => ?_
  rw [qCoeff_heckeFun hp hpN ε _ hg₁ n, qCoeff_heckeU_coe hq.ne_zero _ n, coe_uLin, coe_heckeLin,
    qCoeff_heckeFun hp hpN ε _ f.2 (n * q), qCoeff_heckeU_coe hq.ne_zero _ (n * p)]
  have hpnq : (p ∣ n * q) ↔ p ∣ n :=
    ⟨fun h => Nat.Coprime.dvd_of_dvd_mul_right hpq h, fun h => dvd_mul_of_dvd_left h q⟩
  have h2 : (if p ∣ n then ModularFormClass.qCoeff (heckeU k q ⇑(f : CuspForm (Gamma1 N) k)) (n / p) else 0)
      = (if p ∣ n * q then ModularFormClass.qCoeff (⇑(f : CuspForm (Gamma1 N) k)) (n * q / p) else 0) := by
    by_cases hpn : p ∣ n
    · rw [if_pos hpn, if_pos (hpnq.mpr hpn), qCoeff_heckeU_coe hq.ne_zero, Nat.mul_div_right_comm hpn]
    · rw [if_neg hpn, if_neg (fun h => hpn (hpnq.mp h))]
  rw [h2, mul_right_comm]

end HeckeU

section Bridge

variable [NeZero N] {k : ℤ}

private theorem heckeLin_eq_smul_iff {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (ε : DirichletCharacter ℂ N) (f : nebSpace N k ε) (c : ℂ) :
    heckeLin hp hpN ε f = c • f ↔
      ∀ n : ℕ, ModularFormClass.qCoeff (f : CuspForm (Gamma1 N) k) (p * n) +
          ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then ModularFormClass.qCoeff (f : CuspForm (Gamma1 N) k) (n / p) else 0) =
        c * ModularFormClass.qCoeff (f : CuspForm (Gamma1 N) k) n := by
  constructor
  · intro hL n
    have hfun : heckeFun k ε p ⇑(f : CuspForm (Gamma1 N) k) = c • ⇑(f : CuspForm (Gamma1 N) k) := by
      have := congrArg (fun w : nebSpace N k ε => (⇑(w : CuspForm (Gamma1 N) k) : ℍ → ℂ)) hL
      simp only [Submodule.coe_smul, CuspForm.IsGLPos.coe_smul] at this
      exact this
    have hq := congrArg (fun F : ℍ → ℂ => ModularFormClass.qCoeff F n) hfun
    rw [qCoeff_heckeFun hp hpN ε _ f.2 n, qCoeff_smul_coe] at hq
    rw [mul_comm p n]
    exact hq
  · intro h
    apply Subtype.ext
    apply DFunLike.coe_injective
    change heckeFun k ε p ⇑(f : CuspForm (Gamma1 N) k) = ⇑((c • f : nebSpace N k ε) : CuspForm (Gamma1 N) k)
    rw [Submodule.coe_smul, CuspForm.IsGLPos.coe_smul]
    have r₁ : Reg (heckeFun k ε p ⇑(f : CuspForm (Gamma1 N) k)) := reg_coe (heckeForm hp hpN ε _ f.2)
    have r₂ : Reg (c • (⇑(f : CuspForm (Gamma1 N) k) : ℍ → ℂ)) := (reg_coe _).smul c
    refine UpperHalfPlane.eq_of_forall_qCoeff_eq r₁.per r₁.hol r₁.bdd r₂.per r₂.hol r₂.bdd fun n => ?_
    rw [qCoeff_heckeFun hp hpN ε _ f.2 n, qCoeff_smul_coe, mul_comm n p]
    exact h n

private theorem qCoeff_of_uLin_eq_smul {q : ℕ} (hq : q.Prime) (hqN : q ∣ N)
    (ε : DirichletCharacter ℂ N) (f : nebSpace N k ε) (c : ℂ) (hL : uLin hqN ε f = c • f) (n : ℕ) :
    ModularFormClass.qCoeff (f : CuspForm (Gamma1 N) k) (q * n) =
      c * ModularFormClass.qCoeff (f : CuspForm (Gamma1 N) k) n := by
  have hfun : heckeU k q ⇑(f : CuspForm (Gamma1 N) k) = c • ⇑(f : CuspForm (Gamma1 N) k) := by
    have := congrArg (fun w : nebSpace N k ε => (⇑(w : CuspForm (Gamma1 N) k) : ℍ → ℂ)) hL
    simp only [Submodule.coe_smul, CuspForm.IsGLPos.coe_smul] at this
    rw [← this, coe_uLin]
  have hc := congrArg (fun F : ℍ → ℂ => ModularFormClass.qCoeff F n) hfun
  rw [qCoeff_heckeU_coe hq.ne_zero, qCoeff_smul_coe] at hc
  rw [mul_comm q n]
  exact hc

end Bridge

namespace LA

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

private theorem exists_mem_common_eigenvector (S : Set (Module.End K V))
    (hS : ∀ s ∈ S, ∀ t ∈ S, Commute s t) :
    ∀ (n : ℕ) (W : Submodule K V), Module.finrank K W = n → W ≠ ⊥ →
      (∀ s ∈ S, ∀ x ∈ W, s x ∈ W) →
      ∃ v ∈ W, v ≠ 0 ∧ ∀ s ∈ S, ∃ c : K, s v = c • v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hWn hWbot hWinv
  by_cases hscalar : ∀ s ∈ S, ∃ c : K, ∀ x ∈ W, s x = c • x
  · obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWbot
    exact ⟨v, hvW, hv0, fun s hs => (hscalar s hs).imp fun c hc => hc v hvW⟩
  · push Not at hscalar
    obtain ⟨s, hs, hns⟩ := hscalar
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWbot
    let s' : Module.End K W := LinearMap.restrict s (hWinv s hs)
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue s'
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    let W' : Submodule K V := W ⊓ Module.End.eigenspace s μ
    have hW'le : W' ≤ W := inf_le_left
    have hmemW' : ∀ y, y ∈ W' ↔ y ∈ W ∧ s y = μ • y := fun y => by
      rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
    have hsw : s (w : V) = μ • (w : V) := by
      have h := congrArg Subtype.val hw.apply_eq_smul
      rwa [LinearMap.coe_restrict_apply, Submodule.coe_smul] at h
    have hwW' : (w : V) ∈ W' := (hmemW' _).mpr ⟨w.2, hsw⟩
    have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
    have hW'bot : W' ≠ ⊥ := fun h => hw0 ((Submodule.mem_bot K).mp (h ▸ hwW'))
    obtain ⟨x, hxW, hx⟩ := hns μ
    have hW'lt : W' < W := lt_of_le_of_ne hW'le fun h => hx ((hmemW' x).mp (h.ge hxW)).2
    have hrank : Module.finrank K W' < n := hWn ▸ Submodule.finrank_lt_finrank_of_lt hW'lt
    have hW'inv : ∀ t ∈ S, ∀ y ∈ W', t y ∈ W' := by
      intro t ht y hy
      rw [hmemW'] at hy ⊢
      refine ⟨hWinv t ht y hy.1, ?_⟩
      have hc : s (t y) = t (s y) := by
        have := congrArg (fun φ : Module.End K V => φ y) (hS s hs t ht).eq
        simpa using this
      rw [hc, hy.2, map_smul]
    obtain ⟨v, hvW', hv0, hv⟩ := ih _ hrank W' rfl hW'bot hW'inv
    exact ⟨v, hW'le hvW', hv0, hv⟩

private theorem exists_common_eigenvector [Nontrivial V] (S : Set (Module.End K V))
    (hS : ∀ s ∈ S, ∀ t ∈ S, Commute s t) :
    ∃ v : V, v ≠ 0 ∧ ∀ s ∈ S, ∃ c : K, s v = c • v := by
  obtain ⟨v, -, hv0, hv⟩ := exists_mem_common_eigenvector S hS _ ⊤ rfl top_ne_bot
    (fun s _ x _ => Submodule.mem_top)
  exact ⟨v, hv0, hv⟩

end LA

section Assembly

variable [NeZero N] {k : ℤ}

private def GoodPrime (N : ℕ) : Type := {p : ℕ // p.Prime ∧ ¬ p ∣ N}

private def BadPrime (N : ℕ) : Type := {q : ℕ // q.Prime ∧ q ∣ N}

private def heckeFamilySet (ε : DirichletCharacter ℂ N) : Set (Module.End ℂ (nebSpace N k ε)) :=
  Set.range (fun p : GoodPrime N => heckeLin (k := k) p.2.1 p.2.2 ε) ∪
    Set.range (fun q : BadPrime N => uLin (k := k) q.2.2 ε)

private theorem heckeFamilySet_comm (ε : DirichletCharacter ℂ N) :
    ∀ s ∈ heckeFamilySet (k := k) ε, ∀ t ∈ heckeFamilySet (k := k) ε, Commute s t := by
  rintro s (⟨p, rfl⟩ | ⟨q, rfl⟩) t (⟨p', rfl⟩ | ⟨q', rfl⟩)
  · exact heckeLin_comm p.2.1 p.2.2 p'.2.1 p'.2.2 ε
  · exact heckeLin_uLin_comm p.2.1 p.2.2 q'.2.1 q'.2.2 ε
  · exact (heckeLin_uLin_comm p'.2.1 p'.2.2 q.2.1 q.2.2 ε).symm
  · exact uLin_comm q.2.1 q.2.2 q'.2.1 q'.2.2 ε

private theorem main (S : Set ℕ) (ε : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) k) (hf0 : f ≠ 0) (hε : CuspForm.HasNebentypus ε f)
    (a : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ N → ∀ n : ℕ,
      ModularFormClass.qCoeff f (p * n) +
          ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
        a p * ModularFormClass.qCoeff f n) :
    ∃ (g : CuspForm (Gamma1 N) k) (b : ℕ → ℂ),
      g ≠ 0 ∧ CuspForm.HasNebentypus ε g ∧
      (∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ N → b p = a p) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          b p * ModularFormClass.qCoeff g n) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff g (q * n) = b q * ModularFormClass.qCoeff g n) := by
  classical
  haveI : FiniteDimensional ℂ (CuspForm (Gamma1 N) k) := CuspForm.finiteDimensional_of_isArithmetic _ k

  let X : Submodule ℂ (nebSpace N k ε) :=
    { carrier := {h | ∀ p : ℕ, ∀ hp : p.Prime, p ∉ S → ∀ hpN : ¬ p ∣ N, heckeLin hp hpN ε h = a p • h}
      zero_mem' := by
        intro p hp _ hpN
        rw [map_zero, smul_zero]
      add_mem' := by
        intro u v hu hv p hp hpS hpN
        rw [map_add, hu p hp hpS hpN, hv p hp hpS hpN, smul_add]
      smul_mem' := by
        intro c u hu p hp hpS hpN
        rw [map_smul, hu p hp hpS hpN, smul_comm] }
  have hmemX : ∀ h : nebSpace N k ε, h ∈ X ↔
      ∀ p : ℕ, ∀ hp : p.Prime, p ∉ S → ∀ hpN : ¬ p ∣ N, heckeLin hp hpN ε h = a p • h :=
    fun h => Iff.rfl

  have hfX : (⟨f, hε⟩ : nebSpace N k ε) ∈ X := by
    rw [hmemX]
    intro p hp hpS hpN
    exact (heckeLin_eq_smul_iff hp hpN ε ⟨f, hε⟩ (a p)).mpr (hT p hp hpS hpN)
  have hXbot : X ≠ ⊥ := by
    intro h
    have : (⟨f, hε⟩ : nebSpace N k ε) = 0 := (Submodule.mem_bot ℂ).mp (h ▸ hfX)
    exact hf0 (congrArg Subtype.val this)

  have hXinv : ∀ t ∈ heckeFamilySet (k := k) ε, ∀ x ∈ X, t x ∈ X := by
    intro t ht x hx
    rw [hmemX] at hx ⊢
    intro p hp hpS hpN
    have hTmem : heckeLin (k := k) hp hpN ε ∈ heckeFamilySet ε :=
      Or.inl ⟨⟨p, hp, hpN⟩, rfl⟩
    have hc := congrArg (fun φ : Module.End ℂ (nebSpace N k ε) => φ x)
      (heckeFamilySet_comm ε _ hTmem t ht).eq
    simp only [Module.End.mul_apply] at hc
    rw [hc, hx p hp hpS hpN, map_smul]

  obtain ⟨v, hvX, hv0, hv⟩ := LA.exists_mem_common_eigenvector (heckeFamilySet (k := k) ε)
    (heckeFamilySet_comm ε) _ X rfl hXbot hXinv

  let b : ℕ → ℂ := fun p =>
    if hp : p.Prime ∧ ¬ p ∣ N then
      (if p ∈ S then (hv _ (Or.inl ⟨⟨p, hp⟩, rfl⟩)).choose else a p)
    else if hq : p.Prime ∧ p ∣ N then (hv _ (Or.inr ⟨⟨p, hq⟩, rfl⟩)).choose else 0
  have hbT : ∀ p : ℕ, ∀ hp : p.Prime, ∀ hpN : ¬ p ∣ N, heckeLin hp hpN ε v = b p • v := by
    intro p hp hpN
    by_cases hpS : p ∈ S
    · have e : b p = (hv _ (Or.inl ⟨⟨p, hp, hpN⟩, rfl⟩)).choose := by
        simp only [b, dif_pos (show p.Prime ∧ ¬ p ∣ N from ⟨hp, hpN⟩), if_pos hpS]
      rw [e]
      exact (hv _ (Or.inl ⟨⟨p, hp, hpN⟩, rfl⟩)).choose_spec
    · have e : b p = a p := by
        simp only [b, dif_pos (show p.Prime ∧ ¬ p ∣ N from ⟨hp, hpN⟩), if_neg hpS]
      rw [e]
      exact (hmemX v).mp hvX p hp hpS hpN
  have hbU : ∀ q : ℕ, ∀ hq : q.Prime, ∀ hqN : q ∣ N, uLin hqN ε v = b q • v := by
    intro q hq hqN
    have e : b q = (hv _ (Or.inr ⟨⟨q, hq, hqN⟩, rfl⟩)).choose := by
      simp only [b, dif_neg (show ¬ (q.Prime ∧ ¬ q ∣ N) from fun h => h.2 hqN),
        dif_pos (show q.Prime ∧ q ∣ N from ⟨hq, hqN⟩)]
    rw [e]
    exact (hv _ (Or.inr ⟨⟨q, hq, hqN⟩, rfl⟩)).choose_spec
  refine ⟨(v : CuspForm (Gamma1 N) k), b, ?_, v.2, ?_, ?_, ?_⟩
  · exact fun h => hv0 (Subtype.ext h)
  · intro p hp hpS hpN
    simp only [b, dif_pos (show p.Prime ∧ ¬ p ∣ N from ⟨hp, hpN⟩), if_neg hpS]
  · intro p hp hpN n
    exact (heckeLin_eq_smul_iff hp hpN ε v (b p)).mp (hbT p hp hpN) n
  · intro q hq hqN n
    exact qCoeff_of_uLin_eq_smul hq hqN ε v (b q) (hbU q hq hqN) n

end Assembly

end RefineEigenformG3a

end

open scoped MatrixGroups ModularForm in

theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (S : Set ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hf0 : f ≠ 0) (hε : CuspForm.HasNebentypus ε f)
    (a : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ M → ∀ n : ℕ,
      ModularFormClass.qCoeff f (p * n) +
          ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
        a p * ModularFormClass.qCoeff f n) :
    ∃ (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (b : ℕ → ℂ),
      g ≠ 0 ∧ CuspForm.HasNebentypus ε g ∧
      (∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ M → b p = a p) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          b p * ModularFormClass.qCoeff g n) ∧
      (∀ q : ℕ, q.Prime → q ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff g (q * n) = b q * ModularFormClass.qCoeff g n) :=
  RefineEigenformG3a.main S ε f hf0 hε a hT

end S_CuspForm_exists_hasNebentypus_qCoeff_hecke_eigen_forall_of_qCoeff_hecke_eigen_of_not_mem
end P2MW
export P2MW.S_CuspForm_exists_hasNebentypus_qCoeff_hecke_eigen_forall_of_qCoeff_hecke_eigen_of_not_mem (solution)
