-- Prove2me | solution 1 for ExtCitation.extVanishingCts_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f5d46212-1b33-502a-bfdb-67f674965897

import Definitions.Def_ExtCitation_AdmissibleExtension_v2
import Theorems.Thm_AlgebraicClosure_stabilizer_primitiveRoot_three_le_of_isOpen_of_forall_inertia_inf_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_extVanishingCts_three

set_option autoImplicit false

open ExtCitation

section iface

variable {ζ : AlgebraicClosure ℚ}

private theorem p3b_apply_eq_pow_cycloExp (hζ : IsPrimitiveRoot ζ 3)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :
    σ ζ = ζ ^ cycloExp 3 σ := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  exact modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self 3)
    (σ : (AlgebraicClosure ℚ) ≃+* (AlgebraicClosure ℚ)) hζ.toRootsOfUnity.2

private theorem p3b_cycloExp_lt (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :
    cycloExp 3 σ < 3 :=
  ZMod.val_lt _

private theorem p3b_cycloExp_eq_one_of_fix (hζ : IsPrimitiveRoot ζ 3)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ζ = ζ) :
    cycloExp 3 σ = 1 :=
  hζ.pow_inj (p3b_cycloExp_lt σ) (by norm_num)
    (by rw [← p3b_apply_eq_pow_cycloExp hζ σ, pow_one, hσ])

local notation "Qbar" => AlgebraicClosure ℚ

private theorem p3b_Normal_Qbar : Normal ℚ Qbar := by
  have h : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
  exact h
private theorem p3b_IsAlgebraic_Qbar : Algebra.IsAlgebraic ℚ Qbar := by
  have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
    inferInstance
  exact h

private theorem p3b_exists_conj {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ 3) :
    ∃ c : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), c ζ = ζ ^ 2 := by
  haveI := p3b_Normal_Qbar
  haveI := p3b_IsAlgebraic_Qbar
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) 3 := hζ.pow_of_coprime 2 (by decide)
  have hminpoly : Polynomial.cyclotomic 3 ℚ = minpoly ℚ ζ :=
    Polynomial.cyclotomic_eq_minpoly_rat hζ (by decide)
  have hroot : Polynomial.aeval (ζ ^ 2) (minpoly ℚ ζ) = 0 := by
    rw [← hminpoly]
    have := hζ2.isRoot_cyclotomic (R := Qbar) (n := 3) (by decide)
    rw [Polynomial.aeval_def, ← Polynomial.eval_map,
      Polynomial.map_cyclotomic 3 (algebraMap ℚ Qbar)]
    exact this
  have halg : IsAlgebraic ℚ ζ := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) ζ)
  exact minpoly.exists_algEquiv_of_root' halg hroot

private theorem p3b_splitsGlobally (V : Type) [AddCommGroup V] [Module (ZMod 3) V]
    [DistribMulAction ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) V]
    [SMulCommClass ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (ZMod 3) V]
    (C : Submodule (ZMod 3) V)
    (hζ : IsPrimitiveRoot ζ 3)
    (hsub : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∀ x ∈ C, σ • x = x)
    (hquot : ∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (x : V),
      σ • x - (cycloExp 3 σ : ZMod 3) • x ∈ C)
    (htriv : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), σ ζ = ζ → ∀ x : V, σ • x = x) :
    SplitsGlobally C := by
  obtain ⟨c, hc⟩ := p3b_exists_conj hζ
  have hspec := p3b_apply_eq_pow_cycloExp hζ
  have h3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hpow4 : ζ ^ (2 * 2) = ζ := by
    calc ζ ^ (2 * 2) = ζ ^ 3 * ζ := by ring
      _ = ζ := by rw [h3, one_mul]

  have hcc : (c * c) ζ = ζ := by
    rw [AlgEquiv.mul_apply, hc, map_pow, hc, ← pow_mul, hpow4]
  have hcc' : ∀ x : V, c • c • x = x := fun x => by
    rw [← mul_smul]; exact htriv _ hcc x

  have hdich : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
      (∀ x : V, σ • x = x) ∨ (∀ x : V, σ • x = c • x) := by
    intro σ
    have hk := hspec σ
    have hklt := p3b_cycloExp_lt σ
    obtain h0 | h1 | h2 : cycloExp 3 σ = 0 ∨ cycloExp 3 σ = 1 ∨ cycloExp 3 σ = 2 := by omega
    · exfalso
      rw [h0, pow_zero] at hk
      exact hζ.ne_one (by norm_num) (σ.injective (by rw [hk, map_one]))
    · left
      rw [h1, pow_one] at hk
      exact htriv σ hk
    · right
      rw [h2] at hk
      have hcs : (c * σ) ζ = ζ := by
        rw [AlgEquiv.mul_apply, hk, map_pow, hc, ← pow_mul, hpow4]
      intro x
      have hx := htriv _ hcs x
      rw [mul_smul] at hx
      calc σ • x = c • c • σ • x := (hcc' _).symm
        _ = c • x := by rw [hx]

  let C' : Submodule (ZMod 3) V :=
    { carrier := {v | c • v = -v}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [smul_add, ha, hb, neg_add]
      zero_mem' := by simp only [Set.mem_setOf_eq, smul_zero, neg_zero]
      smul_mem' := fun r v hv => by
        simp only [Set.mem_setOf_eq] at hv ⊢
        rw [smul_comm c r v, hv, smul_neg] }
  have hmemC' : ∀ v : V, v ∈ C' ↔ c • v = -v := fun _ => Iff.rfl
  have h22 : ((2 : ZMod 3) * 2) = 1 := by decide
  refine ⟨C', ?_, IsCompl.of_eq ?_ ?_⟩
  ·
    intro σ x hx
    rw [hmemC'] at hx ⊢
    rcases hdich σ with hid | hcσ
    · rw [hid]; exact hx
    · rw [hcσ, hx, smul_neg, hx]
  ·
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxC, hxC'⟩ := Submodule.mem_inf.mp hx
    have h1 : c • x = x := hsub c x hxC
    have h2 : c • x = -x := hxC'
    rw [h1] at h2
    have hxx : x + x = 0 := eq_neg_iff_add_eq_zero.mp h2
    calc x = ((2 : ZMod 3) * 2) • x := by rw [h22, one_smul]
      _ = (2 : ZMod 3) • (x + x) := by rw [mul_smul, two_smul (ZMod 3) x]
      _ = 0 := by rw [hxx, smul_zero]
  ·
    rw [Submodule.eq_top_iff']
    intro v
    have hca : c • (v + c • v) = v + c • v := by rw [smul_add, hcc', add_comm]
    have hcb : c • (v - c • v) = -(v - c • v) := by rw [smul_sub, hcc', neg_sub]
    have hexpc : cycloExp 3 c = 2 :=
      hζ.pow_inj (p3b_cycloExp_lt c) (by norm_num) (by rw [← hspec c, hc])
    have haC : v + c • v ∈ C := by
      have h := hquot c (v + c • v)
      rw [hexpc, hca, Nat.cast_ofNat, two_smul] at h
      have h' : v + c • v - (v + c • v + (v + c • v)) = -(v + c • v) := by abel
      rw [h'] at h
      simpa using C.neg_mem h
    have hbC' : v - c • v ∈ C' := hcb
    have hv : v = (2 : ZMod 3) • (v + c • v) + (2 : ZMod 3) • (v - c • v) := by
      rw [← smul_add]
      have h' : v + c • v + (v - c • v) = v + v := by abel
      rw [h', ← two_smul (ZMod 3) v, smul_smul, h22, one_smul]
    rw [hv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.mem_sup_left haC))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_right hbC'))

end iface

theorem solution : ExtCitation.ExtVanishingCts 3 := by
  intro V _ _ _ _ C hadm
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 3

  let N : Subgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :=
    { carrier := {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ) | ∀ v : V, σ • v = v}
      one_mem' := fun v => one_smul _ v
      mul_mem' := fun {a b} ha hb v => by rw [mul_smul, hb v, ha v]
      inv_mem' := fun {a} ha v => by
        conv_lhs => rw [← ha v]
        exact inv_smul_smul a v }
  have hmemN : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
      σ ∈ N ↔ ∀ v : V, σ • v = v := fun _ => Iff.rfl

  have hopen : IsOpen (N : Set ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))) :=
    hadm.open_kernel

  have hN : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime q →
      A.inertiaSubgroupIn ℚ ⊓
        MulAction.stabilizer ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) ζ ≤ N := by
    intro q hq A hA σ hσ
    rw [Subgroup.mem_inf] at hσ
    obtain ⟨hσI, hσS⟩ := hσ
    by_cases hq3 : q = 3
    ·
      subst hq3
      obtain ⟨C', hC'stab, hC'compl⟩ := hadm.locally_split A hA
      have hσD : σ ∈ A.decompositionSubgroup ℚ := Subgroup.map_subtype_le _ hσI
      have hfix : σ ζ = ζ := hσS
      have hexp : cycloExp 3 σ = 1 := p3b_cycloExp_eq_one_of_fix hζ σ hfix
      intro v
      have hv : v ∈ C ⊔ C' := hC'compl.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
      have h1 : σ • y - y ∈ C := by
        have h := hadm.cyclo_quot σ y
        rwa [hexp, Nat.cast_one, one_smul] at h
      have h2 : σ • y - y ∈ C' := sub_mem (hC'stab σ hσD y hy) hy
      have hzero : σ • y - y = 0 :=
        Submodule.disjoint_def.mp hC'compl.disjoint _ h1 h2
      rw [smul_add, hadm.fixed_sub σ x hx, sub_eq_zero.mp hzero]
    ·
      intro v
      exact hadm.unramified_outside q hq hq3 A hA σ hσI v

  have hstab :
      MulAction.stabilizer ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) ζ ≤ N :=
    AlgebraicClosure.stabilizer_primitiveRoot_three_le_of_isOpen_of_forall_inertia_inf_le
      hζ N hopen hN

  have htriv : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
      σ ζ = ζ → ∀ x : V, σ • x = x :=
    fun σ h x => (hmemN σ).mp (hstab (show σ • ζ = ζ from h)) x
  exact p3b_splitsGlobally V C hζ hadm.fixed_sub hadm.cyclo_quot htriv

end S_ExtCitation_extVanishingCts_three
end P2MW
export P2MW.S_ExtCitation_extVanishingCts_three (solution)
