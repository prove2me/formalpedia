-- Prove2me | solution 1 for CuspForm.exists_finset_dirichlet_sum_eq_and_independent_of_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/cee5a7da-16d4-5433-a10c-6782e4c0cc83

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_finset_dirichlet_sum_eq_and_independent_of_gammaH

set_option autoImplicit false

noncomputable section

namespace CuspForm
p2m_export "CuspForm" "zero_at_cusps' IsGLPos.coe_smul coe_zero holo' ext coe_smul coe_add"
namespace GammaHNebentypusDecomp
p2m_open "CuspForm"

open CongruenceSubgroup ModularForm
open scoped MatrixGroups ModularForm

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

private abbrev dd (γ : SL(2, ℤ)) : ZMod M := ((γ 1 1 : ℤ) : ZMod M)

private theorem det_mod (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    ((γ 0 0 : ℤ) : ZMod M) * ((γ 1 1 : ℤ) : ZMod M) = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := by simpa using Gamma0_mem.mp hγ
  have h := γ.det_coe
  rw [Matrix.det_fin_two] at h
  have := congrArg (Int.cast : ℤ → ZMod M) h
  push_cast at this
  rw [hc] at this
  linear_combination this

private theorem dd_mul {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 M) (h₂ : γ₂ ∈ Gamma0 M) :
    dd (M := M) (γ₁ * γ₂) = dd (M := M) γ₁ * dd γ₂ := by
  have := map_mul (Gamma0Map M) ⟨γ₁, h₁⟩ ⟨γ₂, h₂⟩
  exact this

private theorem isUnit_dd {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : IsUnit (dd (M := M) γ) :=
  IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact det_mod γ hγ)

private theorem val_gamma0Units_eq_dd {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ((CohCarrier.gamma0Units M ⟨γ, hγ⟩ : (ZMod M)ˣ) : ZMod M) = dd γ := rfl

private theorem mem_GammaH_of_dd_eq {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) {u : (ZMod M)ˣ} (hu : u ∈ H)
    (h : dd (M := M) γ = (u : ZMod M)) : γ ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨hγ, ?_⟩
  have : CohCarrier.gamma0Units M ⟨γ, hγ⟩ = u := Units.ext (by rw [val_gamma0Units_eq_dd, h])
  rw [this]
  exact hu

private theorem mul_inv_mem_GammaH {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 M) (h₂ : γ₂ ∈ Gamma0 M)
    (h : dd (M := M) γ₁ = dd γ₂) : γ₂ * γ₁⁻¹ ∈ CohCarrier.GammaH M H := by
  have hmem : γ₂ * γ₁⁻¹ ∈ Gamma0 M := mul_mem h₂ (inv_mem h₁)
  refine mem_GammaH_of_dd_eq hmem (one_mem H) ?_
  have hprod : dd (M := M) (γ₂ * γ₁⁻¹) * dd (M := M) γ₁ = dd γ₂ := by
    rw [← dd_mul hmem h₁, inv_mul_cancel_right]
  rw [h] at hprod
  rw [Units.val_one]
  exact (isUnit_dd h₂).mul_left_injective (hprod.trans (one_mul _).symm)

private theorem exists_lift (u : (ZMod M)ˣ) [NeZero M] :
    ∃ σ : SL(2, ℤ), σ ∈ Gamma0 M ∧ dd (M := M) σ = (u : ZMod M) := by
  have hn : (u : ZMod M).val.Coprime M := ZMod.val_coe_unit_coprime u
  obtain ⟨a, b, hab⟩ : IsCoprime ((u : ZMod M).val : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hn
  refine ⟨⟨!![a, -b; (M : ℤ), ((u : ZMod M).val : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination hab
  · rw [Gamma0_mem]; simp
  · simp [dd]

private theorem finiteIndex_GammaH [NeZero M] : (CohCarrier.GammaH M H).FiniteIndex := by
  refine (IsCongruenceSubgroup.finiteIndex ⟨M, NeZero.ne _, fun γ hγ => ?_⟩)
  obtain ⟨-, -, hc, hd⟩ := Gamma_mem.mp hγ
  have hγ0 : γ ∈ Gamma0 M := by rw [Gamma0_mem]; exact hc
  exact mem_GammaH_of_dd_eq hγ0 (one_mem H) (by rw [Units.val_one]; exact hd)

section Slash

variable {k : ℤ}

private theorem sl_slash (f : UpperHalfPlane → ℂ) (γ : SL(2, ℤ)) :
    f ∣[k] γ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) := rfl

private theorem slash_mem (g : CuspForm (CohCarrier.GammaH M H) k) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CohCarrier.GammaH M H) :
    (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑g :=
  SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)

private theorem slash_eq_of_dd_eq (g : CuspForm (CohCarrier.GammaH M H) k) {σ σ' : SL(2, ℤ)}
    (hσ : σ ∈ Gamma0 M) (hσ' : σ' ∈ Gamma0 M) (h : dd (M := M) σ = dd σ') :
    (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
      = (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ' : GL (Fin 2) ℝ) := by
  have hmem : σ' * σ⁻¹ ∈ CohCarrier.GammaH M H := mul_inv_mem_GammaH hσ hσ' h
  conv_rhs => rw [show σ' = (σ' * σ⁻¹) * σ by rw [inv_mul_cancel_right], map_mul,
    SlashAction.slash_mul, slash_mem g hmem]

end Slash

section Diamond

variable [NeZero M] {k : ℤ}

private def diamond (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 M) :
    CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k where
  toFun g :=
    { toFun := (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
      slash_action_eq' := by
        intro A hA
        obtain ⟨γ, hγ, rfl⟩ := hA
        change ((⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)) ∣[k]
          (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = _
        have hconj : σ * γ * σ⁻¹ ∈ CohCarrier.GammaH M H :=
          CohCarrier.conj_mem_GammaH M H ⟨σ, hσ⟩ ⟨γ, hγ⟩
        rw [← SlashAction.slash_mul, ← map_mul,
          show σ * γ = (σ * γ * σ⁻¹) * σ by rw [inv_mul_cancel_right], map_mul,
          SlashAction.slash_mul, slash_mem g hconj]
      holo' := (CuspFormClass.holo g).slash k _
      zero_at_cusps' := by
        haveI : (CohCarrier.GammaH M H).FiniteIndex := finiteIndex_GammaH
        intro c hc A hA
        have hσSL : (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) ∈
            (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ).range := ⟨σ, rfl⟩
        have hc' : IsCusp ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) • c)
            ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
          exact hc.smul_of_mem hσSL
        have := (OnePoint.IsZeroAt.smul_iff (g := (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ))
          (c := c) (f := (⇑g : UpperHalfPlane → ℂ)) (k := k)).mp (CuspFormClass.zero_at_cusps g hc')
        exact this A hA }
  map_add' g h := by
    apply DFunLike.coe_injective
    change ((⇑(g + h) : UpperHalfPlane → ℂ)) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
      = (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
        + (⇑h : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
    rw [CuspForm.coe_add, SlashAction.add_slash]
  map_smul' c g := by
    apply DFunLike.coe_injective
    change ((⇑(c • g) : UpperHalfPlane → ℂ)) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
      = c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ))
    rw [CuspForm.IsGLPos.coe_smul, ← sl_slash, ModularForm.SL_smul_slash, sl_slash]

private def lift (u : (ZMod M)ˣ) : SL(2, ℤ) := (exists_lift (M := M) u).choose

private theorem lift_mem (u : (ZMod M)ˣ) : lift (M := M) u ∈ Gamma0 M :=
  (exists_lift (M := M) u).choose_spec.1

private theorem dd_lift (u : (ZMod M)ˣ) : dd (M := M) (lift u) = (u : ZMod M) :=
  (exists_lift (M := M) u).choose_spec.2

private theorem lift_mem_GammaH {u : (ZMod M)ˣ} (hu : u ∈ H) : lift (M := M) u ∈ CohCarrier.GammaH M H :=
  mem_GammaH_of_dd_eq (lift_mem u) hu (dd_lift u)

private def proj (ε : DirichletCharacter ℂ M) (g : CuspForm (CohCarrier.GammaH M H) k) :
    CuspForm (CohCarrier.GammaH M H) k :=
  ((M.totient : ℂ))⁻¹ •
    ∑ u : (ZMod M)ˣ, ε ((u⁻¹ : (ZMod M)ˣ) : ZMod M) • diamond (lift u) (lift_mem u) g

omit [NeZero M] in
private theorem coe_sum {ι : Type*} (s : Finset ι) (F : ι → CuspForm (CohCarrier.GammaH M H) k) :
    (⇑(∑ i ∈ s, F i) : UpperHalfPlane → ℂ) = ∑ i ∈ s, (⇑(F i) : UpperHalfPlane → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.coe_add, ih]

private theorem coe_proj (ε : DirichletCharacter ℂ M) (g : CuspForm (CohCarrier.GammaH M H) k) :
    (⇑(proj ε g) : UpperHalfPlane → ℂ) = ((M.totient : ℂ))⁻¹ •
      ∑ u : (ZMod M)ˣ, ε ((u⁻¹ : (ZMod M)ˣ) : ZMod M) •
        ((⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (lift u) : GL (Fin 2) ℝ)) := by
  rw [proj, CuspForm.IsGLPos.coe_smul, coe_sum]
  rfl

private theorem sigma_mapGL (γ : SL(2, ℤ)) (c : ℂ) :
    UpperHalfPlane.σ (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) c = c := by
  rw [UpperHalfPlane.σ, if_pos (by simp)]
  rfl

private theorem proj_slash (ε : DirichletCharacter ℂ M) (g : CuspForm (CohCarrier.GammaH M H) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(proj ε g) : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = ε (dd γ) • ⇑(proj ε g) := by
  set d₀ : (ZMod M)ˣ := (isUnit_dd hγ).unit with hd₀
  have hd₀' : (d₀ : ZMod M) = dd γ := (isUnit_dd hγ).unit_spec
  rw [coe_proj, ModularForm.smul_slash, SlashAction.sum_slash]
  simp_rw [sigma_mapGL, ModularForm.smul_slash, sigma_mapGL, ← SlashAction.slash_mul, ← map_mul]
  have hstep : ∀ u : (ZMod M)ˣ,
      (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (lift u * γ) : GL (Fin 2) ℝ)
        = (⇑g : UpperHalfPlane → ℂ) ∣[k]
            (Matrix.SpecialLinearGroup.mapGL ℝ (lift (u * d₀)) : GL (Fin 2) ℝ) := by
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
  rw [show (u⁻¹ : (ZMod M)ˣ) = d₀ * (u * d₀)⁻¹ by group, Units.val_mul, map_mul, hd₀']

private theorem sum_proj (g : CuspForm (CohCarrier.GammaH M H) k) :
    ∑ ε : DirichletCharacter ℂ M, proj ε g = g := by
  apply DFunLike.coe_injective
  change (⇑(∑ ε : DirichletCharacter ℂ M, proj ε g) : UpperHalfPlane → ℂ) = ⇑g
  rw [coe_sum]
  simp_rw [coe_proj]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hφ : ((M.totient : ℂ)) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos M)).ne'
  have horth : ∀ u : (ZMod M)ˣ,
      ∑ ε : DirichletCharacter ℂ M, ε ((u⁻¹ : (ZMod M)ˣ) : ZMod M)
        = if u = 1 then (M.totient : ℂ) else 0 := by
    intro u
    haveI : NeZero (Monoid.exponent (ZMod M)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
    have := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit u) 1
    simp only [map_one, mul_one, ZMod.inv_coe_unit, Units.val_eq_one] at this
    exact this
  simp_rw [← Finset.sum_smul, horth, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, smul_smul, inv_mul_cancel₀ hφ, one_smul]
  exact slash_mem g (lift_mem_GammaH (one_mem H))

private theorem proj_eq_zero_of_apply_ne_one (ε : DirichletCharacter ℂ M)
    (g : CuspForm (CohCarrier.GammaH M H) k) {d : (ZMod M)ˣ} (hd : d ∈ H)
    (hε : ε (d : ZMod M) ≠ 1) : proj ε g = 0 := by
  have h1 := proj_slash ε g (lift d) (lift_mem d)
  rw [slash_mem (proj ε g) (lift_mem_GammaH hd), dd_lift] at h1
  have h2 : (ε (d : ZMod M) - 1) • (⇑(proj ε g) : UpperHalfPlane → ℂ) = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  rw [smul_eq_zero, sub_eq_zero] at h2
  exact DFunLike.coe_injective ((h2.resolve_left hε).trans CuspForm.coe_zero.symm)

private theorem sum_inv_mul_eq (ε₀ ε : DirichletCharacter ℂ M) :
    ∑ u : (ZMod M)ˣ, ε₀ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * ε (u : ZMod M)
      = if ε₀ = ε then (M.totient : ℂ) else 0 := by
  split_ifs with h
  · subst h
    have : ∀ u : (ZMod M)ˣ, ε₀ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * ε₀ (u : ZMod M) = 1 := by
      intro u
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul, mul_one]
  ·
    obtain ⟨u₀, hu₀⟩ : ∃ u₀ : (ZMod M)ˣ, ε₀ (u₀ : ZMod M) ≠ ε (u₀ : ZMod M) := by
      by_contra hall
      push Not at hall
      exact h (MulChar.ext hall)
    set c : ℂ := ε₀ ((u₀⁻¹ : (ZMod M)ˣ) : ZMod M) * ε (u₀ : ZMod M) with hc
    have hc1 : c ≠ 1 := by
      intro h1
      apply hu₀
      have e : ε₀ (u₀ : ZMod M) * c = ε (u₀ : ZMod M) := by
        rw [hc, ← mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
          one_mul]
      rw [h1, mul_one] at e
      exact e
    set S : ℂ := ∑ u : (ZMod M)ˣ, ε₀ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * ε (u : ZMod M) with hS
    have hreindex : S = c * S := by
      rw [hS, Finset.mul_sum]
      refine (Fintype.sum_equiv (Equiv.mulLeft u₀) _ _ fun u => ?_).symm
      simp only [Equiv.coe_mulLeft]
      rw [hc, mul_inv_rev, Units.val_mul, Units.val_mul, map_mul, map_mul]
      ring
    have : (1 - c) * S = 0 := by rw [sub_mul, one_mul, ← hreindex, sub_self]
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (sub_eq_zero.mp h0).symm hc1
    · exact h0

private theorem indep (s : Finset (DirichletCharacter ℂ M))
    (g : DirichletCharacter ℂ M → CuspForm (CohCarrier.GammaH M H) k)
    (hg : ∀ ε ∈ s, ∀ σ : Gamma0 M,
      ⇑(g ε) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • ⇑(g ε))
    (hsum : (∑ ε ∈ s, ⇑(g ε)) = 0) : ∀ ε ∈ s, g ε = 0 := by
  classical
  intro ε₀ hε₀

  let Q : (UpperHalfPlane → ℂ) → (UpperHalfPlane → ℂ) := fun F =>
    ∑ u : (ZMod M)ˣ, ε₀ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) •
      (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (lift (M := M) u) : GL (Fin 2) ℝ))
  have hQ := congrArg Q hsum
  have hQ0 : Q 0 = 0 := by
    simp only [Q, SlashAction.zero_slash, smul_zero, Finset.sum_const_zero]
  have hQs : Q (∑ ε ∈ s, ⇑(g ε)) = (M.totient : ℂ) • ⇑(g ε₀) := by
    simp only [Q, SlashAction.sum_slash, Finset.smul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ ε ∈ s, ∀ u : (ZMod M)ˣ,
        ε₀ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) •
            ((⇑(g ε) : UpperHalfPlane → ℂ) ∣[k]
              (Matrix.SpecialLinearGroup.mapGL ℝ (lift (M := M) u) : GL (Fin 2) ℝ))
          = (ε₀ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * ε (u : ZMod M)) • ⇑(g ε) := by
      intro ε hε u
      rw [hg ε hε ⟨lift u, lift_mem u⟩, smul_smul]
      congr 2
      exact congrArg ε (dd_lift u)
    rw [Finset.sum_congr rfl fun ε hε => (Finset.sum_congr rfl fun u _ => hterm ε hε u)]
    simp_rw [← Finset.sum_smul, sum_inv_mul_eq, ite_smul, zero_smul, Finset.sum_ite_eq s ε₀,
      if_pos hε₀]
  rw [hQs, hQ0, smul_eq_zero] at hQ
  have hφ : ((M.totient : ℂ)) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos M)).ne'
  exact DFunLike.coe_injective ((hQ.resolve_left hφ).trans CuspForm.coe_zero.symm)

end Diamond

end CuspForm.GammaHNebentypusDecomp

end

open scoped MatrixGroups ModularForm in
open CuspForm.GammaHNebentypusDecomp in

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    (∀ f : CuspForm (CohCarrier.GammaH M H) k,
      ∃ (s : Finset (DirichletCharacter ℂ M)) (fε : DirichletCharacter ℂ M → CuspForm (CohCarrier.GammaH M H) k),
        (∀ ε ∈ s, ∀ d : (ZMod M)ˣ, d ∈ H → ε (d : ZMod M) = 1) ∧
        (∀ ε ∈ s, ∀ σ : CongruenceSubgroup.Gamma0 M,
          ⇑(fε ε) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
            ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • ⇑(fε ε)) ∧
        ⇑f = ∑ ε ∈ s, ⇑(fε ε)) ∧
    (∀ (s : Finset (DirichletCharacter ℂ M)) (g : DirichletCharacter ℂ M → CuspForm (CohCarrier.GammaH M H) k),
      (∀ ε ∈ s, ∀ σ : CongruenceSubgroup.Gamma0 M,
          ⇑(g ε) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
            ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • ⇑(g ε)) →
      (∑ ε ∈ s, ⇑(g ε)) = 0 → ∀ ε ∈ s, g ε = 0) := by
  classical
  refine ⟨fun f => ?_, fun s g hg hsum => indep s g hg hsum⟩
  refine ⟨Finset.univ.filter (fun ε : DirichletCharacter ℂ M => ∀ d : (ZMod M)ˣ, d ∈ H → ε (d : ZMod M) = 1),
    fun ε => proj ε f, ?_, ?_, ?_⟩
  · intro ε hε
    exact (Finset.mem_filter.mp hε).2
  · intro ε _ σ
    exact proj_slash ε f (σ : SL(2, ℤ)) σ.2
  · rw [Finset.sum_filter_of_ne, ← coe_sum, sum_proj]
    intro ε _ hne d hd
    by_contra hεd
    apply hne
    show (⇑(proj ε f) : UpperHalfPlane → ℂ) = 0
    rw [proj_eq_zero_of_apply_ne_one ε f hd hεd, CuspForm.coe_zero]

end S_CuspForm_exists_finset_dirichlet_sum_eq_and_independent_of_gammaH
end P2MW
export P2MW.S_CuspForm_exists_finset_dirichlet_sum_eq_and_independent_of_gammaH (solution)
