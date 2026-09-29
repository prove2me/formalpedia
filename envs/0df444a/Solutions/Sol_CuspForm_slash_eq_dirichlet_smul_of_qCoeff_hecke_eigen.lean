-- Prove2me | solution 1 for CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/646c6699-5d72-5631-a210-050edc51d9dc

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
import Theorems.Thm_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Theorems.Thm_UpperHalfPlane_qCoeff_heckeU
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CongruenceSubgroup ModularForm UpperHalfPlane Filter Function
open scoped ModularForm UpperHalfPlane MatrixGroups

noncomputable section

namespace NebentypusDetect

variable {M : ℕ}

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₀(" M ")" => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

theorem det_mod {N : ℕ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hγ
  have := congrArg (Int.cast : ℤ → ZMod N) (det_eq γ)
  push_cast at this
  rw [hc] at this
  linear_combination this

def dd {N : ℕ} (γ : SL(2, ℤ)) : ZMod N := ((γ 1 1 : ℤ) : ZMod N)

theorem dd_mul {N : ℕ} {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 N) (h₂ : γ₂ ∈ Gamma0 N) :
    dd (N := N) (γ₁ * γ₂) = dd (N := N) γ₁ * dd γ₂ := by
  have := map_mul (Gamma0Map N) ⟨γ₁, h₁⟩ ⟨γ₂, h₂⟩
  exact this

theorem isUnit_dd {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) : IsUnit (dd (N := N) γ) :=
  IsUnit.of_mul_eq_one _ (by rw [dd, mul_comm]; exact det_mod γ hγ)

theorem mem_Gamma1_iff_dd {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    γ ∈ Gamma1 N ↔ dd (N := N) γ = 1 := by
  rw [Gamma1_mem, dd]
  constructor
  · rintro ⟨-, h, -⟩; simpa using h
  · intro hd
    have ha : ((γ 0 0 : ℤ) : ZMod N) = 1 := by
      have := det_mod γ hγ; rw [hd, mul_one] at this; exact this
    exact ⟨by simpa using ha, by simpa using hd, by simpa using Gamma0_mem.mp hγ⟩

theorem inv_mul_mem_Gamma1 {N : ℕ} {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 N) (h₂ : γ₂ ∈ Gamma0 N)
    (h : dd (N := N) γ₁ = dd γ₂) : γ₁⁻¹ * γ₂ ∈ Gamma1 N := by
  have hmem : γ₁⁻¹ * γ₂ ∈ Gamma0 N := mul_mem (inv_mem h₁) h₂
  rw [mem_Gamma1_iff_dd hmem]
  have hprod : dd (N := N) γ₁ * dd (N := N) (γ₁⁻¹ * γ₂) = dd γ₂ := by
    rw [← dd_mul h₁ hmem, mul_inv_cancel_left]
  rw [h] at hprod
  exact (isUnit_dd h₂).mul_right_injective (hprod.trans (mul_one _).symm)

theorem conj_mem_Gamma1 {N : ℕ} {σ γ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 N) (hγ : γ ∈ Gamma1 N) :
    σ * γ * σ⁻¹ ∈ Gamma1 N := by
  have hγ0 : γ ∈ Gamma0 N := Gamma1_in_Gamma0 N hγ
  have hmem : σ * γ * σ⁻¹ ∈ Gamma0 N := mul_mem (mul_mem hσ hγ0) (inv_mem hσ)
  rw [mem_Gamma1_iff_dd hmem]
  have h1 : dd (N := N) γ = 1 := (mem_Gamma1_iff_dd hγ0).mp hγ
  have hprod : dd (N := N) (σ * γ * σ⁻¹) * dd (N := N) σ = dd σ := by
    rw [← dd_mul hmem hσ, inv_mul_cancel_right, dd_mul hσ hγ0, h1, mul_one]
  exact (isUnit_dd hσ).mul_left_injective (hprod.trans (one_mul _).symm)

theorem exists_lift (n : ℕ) (hn : n.Coprime M) :
    ∃ σ : SL(2, ℤ), σ ∈ Gamma0 M ∧ dd (N := M) σ = n := by
  obtain ⟨u, v, huv⟩ : IsCoprime (n : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hn
  refine ⟨⟨!![u, -v; (M : ℤ), (n : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination huv
  · rw [Gamma0_mem]; simp
  · simp [dd]

section Slash

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

theorem isBoundedAtImInfty_slash_heckeMatrix (hp : p ≠ 0) (j : ℕ) {F : ℍ → ℂ}
    (hF : IsBoundedAtImInfty F) : IsBoundedAtImInfty (F ∣[k] heckeMatrix p j) :=
  hF.slash k (by simp [val_heckeMatrix hp])

theorem isBoundedAtImInfty_slash_heckeDiagMatrix (hp : p ≠ 0) {F : ℍ → ℂ}
    (hF : IsBoundedAtImInfty F) : IsBoundedAtImInfty (F ∣[k] heckeDiagMatrix p) :=
  hF.slash k (by simp [val_heckeDiagMatrix hp])

theorem isBoundedAtImInfty_heckeU (hp : p ≠ 0) {F : ℍ → ℂ} (hF : IsBoundedAtImInfty F) :
    IsBoundedAtImInfty (heckeU k p F) := by
  rw [heckeU_def]
  induction (Finset.range p) using Finset.induction_on with
  | empty => (simp; exact (Filter.zero_zeroAtFilter atImInfty).boundedAtFilter)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (isBoundedAtImInfty_slash_heckeMatrix hp j hF).add ih

theorem mdifferentiable_heckeU {F : ℍ → ℂ}
    (hF : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (heckeU k p F) := by
  rw [heckeU_def]
  induction (Finset.range p) using Finset.induction_on with
  | empty => (simp; exact mdifferentiable_const)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hF.slash k _).add ih

end Slash

section Prime

variable [NeZero M] {k : ℤ}

theorem periodic_add_smul {F G : ℍ → ℂ} (hF : Periodic (F ∘ ofComplex) 1)
    (hG : Periodic (G ∘ ofComplex) 1) (c : ℂ) : Periodic ((F + c • G) ∘ ofComplex) 1 := by
  intro w
  have h1 := hF w
  have h2 := hG w
  simp only [comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  rw [h1, h2]

theorem periodic_smul {G : ℍ → ℂ} (hG : Periodic (G ∘ ofComplex) 1) (c : ℂ) :
    Periodic ((c • G) ∘ ofComplex) 1 := by
  intro w
  have h2 := hG w
  simp only [comp_apply, Pi.smul_apply, smul_eq_mul] at h2 ⊢
  rw [h2]

theorem slash_eq_smul_prime (g : CuspForm Γ₁(M) k) (χ : DirichletCharacter ℂ M)
    {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M)
    (heig : ∃ lam : ℂ, ∀ n : ℕ,
      ModularFormClass.qCoeff (⇑g) (n * p)
        + χ (p : ZMod M) * (p : ℂ) ^ (k - 1)
            * (if p ∣ n then ModularFormClass.qCoeff (⇑g) (n / p) else 0)
        = lam * ModularFormClass.qCoeff (⇑g) n)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 M) (hσp : dd (N := M) σ = (p : ZMod M)) :
    (⇑g : ℍ → ℂ) ∣[k] σ = χ (p : ZMod M) • (⇑g : ℍ → ℂ) := by
  obtain ⟨lam, hlam⟩ := heig
  have hp0 : p ≠ 0 := hp.ne_zero
  set c : ℂ := χ (p : ZMod M) with hc

  have hgT : ∀ n : ℕ, (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ n)) = ⇑g :=
    fun n => SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ (T_pow_mem_Gamma1 M n))
  have hgper : Periodic (⇑g ∘ ofComplex) 1 := periodic_of_slash_T (by simpa using hgT 1)
  have hghol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑g) := g.holo'
  have hgbdd : IsBoundedAtImInfty (⇑g) := ModularFormClass.bdd_at_infty g

  set gσ : ℍ → ℂ := (⇑g : ℍ → ℂ) ∣[k] σ with hgσ
  have hgσ_inv : ∀ γ : SL(2, ℤ), γ ∈ Gamma1 M → gσ ∣[k] γ = gσ := by
    intro γ hγ
    rw [hgσ, ← SlashAction.slash_mul, show σ * γ = (σ * γ * σ⁻¹) * σ by rw [inv_mul_cancel_right],
      SlashAction.slash_mul]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ (conj_mem_Gamma1 hσ hγ))

  set U : ℍ → ℂ := heckeU k p (⇑g) with hU
  set D : ℍ → ℂ := (⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix p with hD
  set T' : ℍ → ℂ := U + gσ ∣[k] heckeDiagMatrix p with hT'
  have hT'_inv : ∀ γ ∈ Γ₁(M), T' ∣[k] γ = T' := fun γ hγ =>
    ModularForm.heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1 k hp hpM
      (fun γ' hγ' => SlashInvariantFormClass.slash_action_eq g γ' hγ') σ hσ hσp γ hγ

  have hDT : D ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = D :=
    slash_heckeDiagMatrix_slash_T hp0 (hgT p)
  have hgσδT : (gσ ∣[k] heckeDiagMatrix p) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = gσ ∣[k] heckeDiagMatrix p :=
    slash_heckeDiagMatrix_slash_T hp0 (hgσ_inv _ (T_pow_mem_Gamma1 M p))
  have hUT : U ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = U := by
    have hUeq : U = T' - gσ ∣[k] heckeDiagMatrix p := by rw [hT', add_sub_cancel_right]
    rw [hUeq, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
      hT'_inv _ (Subgroup.mem_map_of_mem _ (T_mem_Gamma1 M)), hgσδT]
  have hUper : Periodic (U ∘ ofComplex) 1 := periodic_of_slash_T hUT
  have hDper : Periodic (D ∘ ofComplex) 1 := periodic_of_slash_T hDT
  have hUhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U :=
    mdifferentiable_heckeU hghol
  have hDhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) D :=
    hghol.slash k _
  have hUbdd : IsBoundedAtImInfty U := isBoundedAtImInfty_heckeU hp0 hgbdd
  have hDbdd : IsBoundedAtImInfty D := isBoundedAtImInfty_slash_heckeDiagMatrix hp0 hgbdd

  set φ : ℍ → ℂ := U + c • D with hφ
  have hφper : Periodic (φ ∘ ofComplex) 1 := periodic_add_smul hUper hDper c
  have hφhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) φ :=
    hUhol.add (hDhol.const_smul c)
  have hφbdd : IsBoundedAtImInfty φ := hUbdd.add (hDbdd.smul c)

  have hanU := analyticAt_cuspFunction_zero one_pos hUper hUhol hUbdd
  have hancD : AnalyticAt ℂ (cuspFunction 1 (c • D)) 0 :=
    analyticAt_cuspFunction_zero one_pos (periodic_smul hDper c) (hDhol.const_smul c) (hDbdd.smul c)
  have hanD := analyticAt_cuspFunction_zero one_pos hDper hDhol hDbdd
  have hang := analyticAt_cuspFunction_zero one_pos hgper hghol hgbdd

  set G : ℍ → ℂ := fun τ => g (heckeDiagMatrix p • τ) with hG
  have hDG : D = ((p : ℂ) ^ (k - 1)) • G := by
    funext τ
    rw [hD, slash_heckeDiagMatrix_apply k hp0, Pi.smul_apply, smul_eq_mul]
  have hpk : ((p : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp0)
  have hGD : G = ((p : ℂ) ^ (k - 1))⁻¹ • D := by
    rw [hDG, smul_smul, inv_mul_cancel₀ hpk, one_smul]
  have hanG : AnalyticAt ℂ (cuspFunction 1 G) 0 := by
    rw [hGD]
    exact analyticAt_cuspFunction_zero one_pos (periodic_smul hDper _) (hDhol.const_smul _)
      (hDbdd.smul _)
  have hqD : ∀ n, ModularFormClass.qCoeff D n
      = (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff (⇑g) (n / p) else 0) := by
    intro n
    rw [ModularFormClass.qCoeff, hDG, qExpansion_smul hanG, map_smul, smul_eq_mul]
    congr 1
    exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul hgper hghol hgbdd hp0 n
  have hqU : ∀ n, ModularFormClass.qCoeff U n = ModularFormClass.qCoeff (⇑g) (n * p) := by
    intro n
    rw [hU, UpperHalfPlane.qCoeff_heckeU hgper hghol hgbdd k hp0 n, coeffHeckeU_apply]
  have hqφ : ∀ n, ModularFormClass.qCoeff φ n = ModularFormClass.qCoeff (lam • (⇑g : ℍ → ℂ)) n := by
    intro n
    rw [ModularFormClass.qCoeff, ModularFormClass.qCoeff, hφ, qExpansion_add hanU hancD,
      qExpansion_smul hanD, qExpansion_smul hang, map_add, map_smul, map_smul, smul_eq_mul,
      smul_eq_mul]
    have h1 := hqU n
    have h2 := hqD n
    have h3 := hlam n
    simp only [ModularFormClass.qCoeff] at h1 h2 h3 ⊢
    rw [h1, h2, ← h3, mul_assoc]

  have hφeq : φ = lam • (⇑g : ℍ → ℂ) :=
    UpperHalfPlane.eq_of_forall_qCoeff_eq hφper hφhol hφbdd (periodic_smul hgper lam)
      (hghol.const_smul lam) (hgbdd.smul lam) hqφ

  set hf : ℍ → ℂ := gσ - c • (⇑g : ℍ → ℂ) with hhf
  have hσδ : UpperHalfPlane.σ (heckeDiagMatrix p) c = c := by
    rw [σ_heckeDiagMatrix]; rfl
  have hhfδ : hf ∣[k] heckeDiagMatrix p = T' - lam • (⇑g : ℍ → ℂ) := by
    rw [hhf, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ModularForm.smul_slash,
      hσδ, ← hφeq, hφ, hT']
    abel
  have hhy : ∀ γ ∈ Γ₁(M), (hf ∣[k] heckeDiagMatrix p) ∣[k] γ = hf ∣[k] heckeDiagMatrix p := by
    intro γ hγ
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    rw [hhfδ, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
      hT'_inv _ (Subgroup.mem_map_of_mem _ hγ₀)]
    congr 2
    change (lam • (⇑g : ℍ → ℂ)) ∣[k] γ₀ = lam • (⇑g : ℍ → ℂ)
    rw [ModularForm.SL_smul_slash]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ₀)

  have hσSL : Matrix.SpecialLinearGroup.mapGL ℝ σ ∈ 𝒮ℒ := ⟨σ, rfl⟩
  let hC : CuspForm Γ₁(M) k :=
    { toFun := hf
      slash_action_eq' := by
        intro A hA
        obtain ⟨γ, hγ, rfl⟩ := hA
        change hf ∣[k] γ = hf
        rw [hhf, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, hgσ_inv γ hγ,
          ModularForm.SL_smul_slash]
        congr 3
        exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)
      holo' := (hghol.slash k _).sub (hghol.const_smul c)
      zero_at_cusps' := by
        intro cusp hcusp A hA
        have hcusp' : IsCusp (Matrix.SpecialLinearGroup.mapGL ℝ σ • cusp) Γ₁(M) := by
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hcusp ⊢
          exact hcusp.smul_of_mem hσSL
        have h1 : IsZeroAtImInfty (gσ ∣[k] A) := by
          have := (OnePoint.IsZeroAt.smul_iff (g := Matrix.SpecialLinearGroup.mapGL ℝ σ)
            (c := cusp) (f := (⇑g : ℍ → ℂ)) (k := k)).mp (CuspFormClass.zero_at_cusps g hcusp')
          exact this A hA
        have h2 : IsZeroAtImInfty ((⇑g : ℍ → ℂ) ∣[k] A) := CuspFormClass.zero_at_cusps g hcusp A hA
        change IsZeroAtImInfty (hf ∣[k] A)
        rw [hhf, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ModularForm.smul_slash]
        exact h1.add ((h2.smul _).neg) }
  have hC0 : hC = 0 :=
    CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1 hp hpM k hC hhy
  have hf0 : hf = 0 := by
    have := congrArg (fun F : CuspForm Γ₁(M) k => (⇑F : ℍ → ℂ)) hC0
    exact this
  rw [hhf, sub_eq_zero] at hf0
  exact hf0

end Prime

section All

variable [NeZero M] {k : ℤ}

theorem dd_pow {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 M) (r : ℕ) :
    dd (N := M) (σ ^ r) = dd (N := M) σ ^ r := by
  induction r with
  | zero => simp [dd]
  | succ r ih => rw [pow_succ, dd_mul (pow_mem hσ r) hσ, ih, pow_succ]

theorem slash_pow_of_slash_eq_smul (g : ℍ → ℂ) (σ : SL(2, ℤ)) (c : ℂ) (h : g ∣[k] σ = c • g)
    (r : ℕ) : g ∣[k] (σ ^ r) = c ^ r • g := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, SlashAction.slash_mul, ih, ModularForm.SL_smul_slash, h, smul_smul, pow_succ]

theorem exists_lift_slash_eq (g : CuspForm Γ₁(M) k) (χ : DirichletCharacter ℂ M)
    (heig : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∃ lam : ℂ, ∀ n : ℕ,
      ModularFormClass.qCoeff (⇑g) (n * p)
        + χ (p : ZMod M) * (p : ℂ) ^ (k - 1)
            * (if p ∣ n then ModularFormClass.qCoeff (⇑g) (n / p) else 0)
        = lam * ModularFormClass.qCoeff (⇑g) n)
    (n : ℕ) (hn : n.Coprime M) :
    ∃ σ : SL(2, ℤ), σ ∈ Gamma0 M ∧ dd (N := M) σ = (n : ZMod M) ∧
      (⇑g : ℍ → ℂ) ∣[k] σ = χ (n : ZMod M) • (⇑g : ℍ → ℂ) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero =>
    have hM : M = 1 := by simpa using hn
    subst hM
    refine ⟨1, one_mem _, Subsingleton.elim _ _, ?_⟩
    rw [SlashAction.slash_one, show ((0 : ℕ) : ZMod 1) = 1 from Subsingleton.elim _ _, map_one,
      one_smul]
  | one =>
    refine ⟨1, one_mem _, by simp [dd], ?_⟩
    rw [SlashAction.slash_one, Nat.cast_one, map_one, one_smul]
  | prime_pow p r hp hr =>
    have hpM : ¬ p ∣ M := by
      have : p.Coprime M := Nat.Coprime.coprime_dvd_left (dvd_pow_self p hr.ne') hn
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp this
    obtain ⟨σ, hσ, hσd⟩ := exists_lift (M := M) p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM)
    have base := slash_eq_smul_prime g χ hp hpM (heig p hp hpM) σ hσ hσd
    refine ⟨σ ^ r, pow_mem hσ r, ?_, ?_⟩
    · rw [dd_pow hσ, hσd, Nat.cast_pow]
    · rw [slash_pow_of_slash_eq_smul _ σ _ base r, Nat.cast_pow, map_pow]
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨σa, hσa, hda, hsa⟩ := iha (Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) hn)
    obtain ⟨σb, hσb, hdb, hsb⟩ := ihb (Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) hn)
    refine ⟨σa * σb, mul_mem hσa hσb, ?_, ?_⟩
    · rw [dd_mul hσa hσb, hda, hdb, Nat.cast_mul]
    · rw [SlashAction.slash_mul, hsa, ModularForm.SL_smul_slash, hsb, smul_smul, Nat.cast_mul,
        map_mul]

theorem main (g : CuspForm Γ₁(M) k) (χ : DirichletCharacter ℂ M)
    (heig : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∃ lam : ℂ, ∀ n : ℕ,
      ModularFormClass.qCoeff (⇑g) (n * p)
        + χ (p : ZMod M) * (p : ℂ) ^ (k - 1)
            * (if p ∣ n then ModularFormClass.qCoeff (⇑g) (n / p) else 0)
        = lam * ModularFormClass.qCoeff (⇑g) n)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑g : ℍ → ℂ) ∣[k] γ = χ (dd (N := M) γ) • (⇑g : ℍ → ℂ) := by
  obtain ⟨u, hu⟩ := isUnit_dd hγ
  set n : ℕ := (dd (N := M) γ).val with hn
  have hncast : (n : ZMod M) = dd γ := ZMod.natCast_zmod_val _
  have hcop : n.Coprime M := by
    have := ZMod.val_coe_unit_coprime u
    rwa [hu] at this
  obtain ⟨σ, hσ, hdd, hslash⟩ := exists_lift_slash_eq g χ heig n hcop
  have hmem : σ⁻¹ * γ ∈ Gamma1 M := inv_mul_mem_Gamma1 hσ hγ (hdd.trans hncast)
  have hfix : (⇑g : ℍ → ℂ) ∣[k] (σ⁻¹ * γ) = ⇑g :=
    SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hmem)
  have hγeq : γ = σ * (σ⁻¹ * γ) := by rw [mul_inv_cancel_left]
  conv_lhs => rw [hγeq, SlashAction.slash_mul, hslash, ModularForm.SL_smul_slash, hfix, hncast]

end All

end NebentypusDetect
p2m_reactivate "P2MW.S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.NebentypusDetect"

end
p2m_reactivate "P2MW.S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.NebentypusDetect"

open scoped MatrixGroups ModularForm in
theorem solution
    {M : ℕ} [NeZero M] (k : ℤ)
    (g : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (χ : DirichletCharacter ℂ M)
    (heig : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∃ lam : ℂ, ∀ n : ℕ,
      ModularFormClass.qCoeff (⇑g) (n * p)
        + χ (p : ZMod M) * (p : ℂ) ^ (k - 1)
            * (if p ∣ n then ModularFormClass.qCoeff (⇑g) (n / p) else 0)
        = lam * ModularFormClass.qCoeff (⇑g) n)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    (⇑g : UpperHalfPlane → ℂ) ∣[k] γ = χ ((γ 1 1 : ℤ) : ZMod M) • (⇑g : UpperHalfPlane → ℂ) :=
  NebentypusDetect.main g χ heig γ hγ

end S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen
end P2MW
export P2MW.S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen (solution)
