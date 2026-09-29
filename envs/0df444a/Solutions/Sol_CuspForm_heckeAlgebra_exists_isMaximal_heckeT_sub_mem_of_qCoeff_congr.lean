-- Prove2me | solution 1 for CuspForm.heckeAlgebra.exists_isMaximal_heckeT_sub_mem_of_qCoeff_congr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6920cc34-e746-54ee-ba1b-c260ec2fc42e

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeAlgebra_exists_isMaximal_heckeT_sub_mem_of_qCoeff_congr

set_option autoImplicit false

open CuspForm ModularFormClass

namespace RC1
namespace EntryAux

open ModularForm UpperHalfPlane

variable {N' : ℕ} {k : ℤ}

private theorem hΓ₀ : (1 : ℝ) ∈
    (CongruenceSubgroup.Gamma0 N' : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples 1

private theorem hA (f : CuspForm (CongruenceSubgroup.Gamma0 N') k) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ⇑f) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ₀

private theorem qCoeff_add (f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma0 N') k) (m : ℕ) :
    qCoeff ((f₁ + f₂ : CuspForm (CongruenceSubgroup.Gamma0 N') k) : UpperHalfPlane → ℂ) m =
      qCoeff f₁ m + qCoeff f₂ m := by
  show qCoeff (⇑f₁ + ⇑f₂ : UpperHalfPlane → ℂ) m = _
  unfold ModularFormClass.qCoeff
  rw [UpperHalfPlane.qExpansion_add (hA f₁) (hA f₂)]; simp

private theorem qCoeff_intCast_smul (z : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma0 N') k)
    (m : ℕ) :
    qCoeff (((z : ℂ) • f : CuspForm (CongruenceSubgroup.Gamma0 N') k) : UpperHalfPlane → ℂ) m =
      (z : ℂ) * qCoeff f m := by
  show qCoeff ((z : ℂ) • ⇑f : UpperHalfPlane → ℂ) m = _
  unfold ModularFormClass.qCoeff
  rw [UpperHalfPlane.qExpansion_smul (hA f)]; simp

private theorem qCoeff_zsmul (z : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma0 N') k) (m : ℕ) :
    qCoeff ((z • f : CuspForm (CongruenceSubgroup.Gamma0 N') k) : UpperHalfPlane → ℂ) m =
      (z : ℂ) * qCoeff f m := by
  rw [show (z • f : CuspForm (CongruenceSubgroup.Gamma0 N') k) = (z : ℂ) • f from
    (Int.cast_smul_eq_zsmul ℂ z f).symm, qCoeff_intCast_smul]

private theorem cuspForm_coe_eq_zero_of_nonpos_weight [NeZero N'] (hw : k ≤ 0)
    (F : CuspForm (CongruenceSubgroup.Gamma0 N') k) : ⇑F = 0 := by
  let Fm : ModularForm (CongruenceSubgroup.Gamma0 N') k :=
    { toSlashInvariantForm := F.toSlashInvariantForm
      holo' := F.holo'
      bdd_at_cusps' := fun hc g hg =>
        Filter.ZeroAtFilter.boundedAtFilter (F.zero_at_cusps' hc g hg) }
  rcases hw.lt_or_eq with hlt | heq
  · have h0 := ModularForm.isZero_of_neg_weight hlt Fm
    have hFm : ⇑F = ⇑Fm := rfl
    rw [hFm, h0]; rfl
  · subst heq
    obtain ⟨c₀, hc₀⟩ := ModularForm.eq_const_of_weight_zero Fm
    have hinf : IsCusp OnePoint.infty
        (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N')) :=
      Subgroup.isCusp_of_mem_strictPeriods one_pos
        (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N')
    have hz : UpperHalfPlane.IsZeroAtImInfty
        (⇑F ∣[(0 : ℤ)] (1 : Matrix.GeneralLinearGroup (Fin 2) ℝ)) :=
      F.zero_at_cusps' hinf 1 (by simp)
    rw [SlashAction.slash_one] at hz
    have hFm : ⇑F = ⇑Fm := rfl
    rw [hFm, hc₀] at hz ⊢
    have hz' : Filter.Tendsto (Function.const UpperHalfPlane c₀)
        UpperHalfPlane.atImInfty (nhds 0) := hz
    rw [(tendsto_nhds_unique hz' tendsto_const_nhds).symm]; rfl

private theorem qCoeff_cuspForm_zero (m : ℕ) :
    qCoeff ((0 : CuspForm (CongruenceSubgroup.Gamma0 N') k) : UpperHalfPlane → ℂ) m = 0 := by
  have : ((0 : CuspForm (CongruenceSubgroup.Gamma0 N') k) : UpperHalfPlane → ℂ) = 0 := rfl
  rw [this]; unfold ModularFormClass.qCoeff
  rw [UpperHalfPlane.qExpansion_zero]; simp

variable (c : ℕ) (𝔪 : Ideal (integralClosure ℤ ℂ))

private def locZero (f : CuspForm (CongruenceSubgroup.Gamma0 N') k) : Prop :=
  ∀ m : ℕ, m.Coprime c → ∀ x y : integralClosure ℤ ℂ, y ∉ 𝔪 →
    (x : ℂ) = y * qCoeff f m → x ∈ 𝔪

private def locInt (f : CuspForm (CongruenceSubgroup.Gamma0 N') k) : Prop :=
  ∀ m : ℕ, m.Coprime c → ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff f m

variable {c 𝔪}

private theorem locZero_zero : locZero c 𝔪 (0 : CuspForm (CongruenceSubgroup.Gamma0 N') k) := by
  intro m _ x y _ hxy
  rw [qCoeff_cuspForm_zero, mul_zero] at hxy
  exact (Subtype.coe_injective (a₂ := (0 : integralClosure ℤ ℂ)) (by simpa using hxy)) ▸ 𝔪.zero_mem

variable (h𝔪 : 𝔪.IsMaximal)
include h𝔪

private theorem locInt_zero : locInt c 𝔪 (0 : CuspForm (CongruenceSubgroup.Gamma0 N') k) := by
  intro m _
  exact ⟨0, 1, fun h => h𝔪.ne_top ((Ideal.eq_top_iff_one 𝔪).mpr h),
    by rw [qCoeff_cuspForm_zero]; simp⟩

private theorem cancel {x y : integralClosure ℤ ℂ} (hy : y ∉ 𝔪) (hyx : y * x ∈ 𝔪) : x ∈ 𝔪 :=
  (h𝔪.isPrime.mem_or_mem hyx).resolve_left hy

private theorem locZero_add {f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma0 N') k}
    (h₁ : locZero c 𝔪 f₁) (h₁i : locInt c 𝔪 f₁) (h₂ : locZero c 𝔪 f₂) (h₂i : locInt c 𝔪 f₂) :
    locZero c 𝔪 (f₁ + f₂) := by
  intro m hm x y hy hxy
  obtain ⟨x₁, y₁, hy₁, hxy₁⟩ := h₁i m hm
  obtain ⟨x₂, y₂, hy₂, hxy₂⟩ := h₂i m hm
  have hkey : ((y₁ * y₂ * x : integralClosure ℤ ℂ) : ℂ) =
      ((y * (y₂ * x₁ + y₁ * x₂) : integralClosure ℤ ℂ) : ℂ) := by
    push_cast
    rw [hxy, qCoeff_add, hxy₁, hxy₂]; ring
  have heq : y₁ * y₂ * x = y * (y₂ * x₁ + y₁ * x₂) := Subtype.coe_injective hkey
  have hmem : y * (y₂ * x₁ + y₁ * x₂) ∈ 𝔪 :=
    𝔪.mul_mem_left y (𝔪.add_mem (𝔪.mul_mem_left y₂ (h₁ m hm x₁ y₁ hy₁ hxy₁))
      (𝔪.mul_mem_left y₁ (h₂ m hm x₂ y₂ hy₂ hxy₂)))
  exact cancel h𝔪 hy₂ (cancel h𝔪 hy₁ (by rw [← mul_assoc, heq]; exact hmem))

private theorem locInt_add {f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma0 N') k}
    (h₁i : locInt c 𝔪 f₁) (h₂i : locInt c 𝔪 f₂) : locInt c 𝔪 (f₁ + f₂) := by
  intro m hm
  obtain ⟨x₁, y₁, hy₁, hxy₁⟩ := h₁i m hm
  obtain ⟨x₂, y₂, hy₂, hxy₂⟩ := h₂i m hm
  refine ⟨y₂ * x₁ + y₁ * x₂, y₁ * y₂,
    fun h => (h𝔪.isPrime.mem_or_mem h).elim hy₁ hy₂, ?_⟩
  rw [qCoeff_add]; push_cast; rw [hxy₁, hxy₂]; ring

private theorem qCoeff_heckeTLin {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N')
    (f : CuspForm (CongruenceSubgroup.Gamma0 N') k) (m : ℕ) :
    qCoeff ((heckeTLin k hℓ hℓN f : CuspForm (CongruenceSubgroup.Gamma0 N') k) :
        UpperHalfPlane → ℂ) m =
      qCoeff f (m * ℓ) + if ℓ ∣ m then (ℓ : ℂ) ^ (k - 1) * qCoeff f (m / ℓ) else 0 := by
  have _ := h𝔪
  rw [CuspForm.coe_heckeTLin_apply,
    ModularFormClass.qCoeff_heckeT f hΓ₀ hℓ.pos.ne' m, ModularForm.coeffHeckeT_apply]

omit h𝔪 in
private theorem coprime_mul_of_not_dvd {ℓ m : ℕ} (hℓ : ℓ.Prime) (hℓc : ¬ ℓ ∣ c)
    (hm : m.Coprime c) : (m * ℓ).Coprime c :=
  Nat.Coprime.mul_left hm (hℓ.coprime_iff_not_dvd.mpr hℓc)

omit h𝔪 in
private theorem coprime_div_of_not_dvd {ℓ m : ℕ} (hℓm : ℓ ∣ m) (hm : m.Coprime c) :
    (m / ℓ).Coprime c :=
  Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hℓm) hm

private theorem locInt_heckeT (hk1 : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N') (hℓc : ¬ ℓ ∣ c)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N') k} (hf : locInt c 𝔪 f) :
    locInt c 𝔪 (heckeTLin k hℓ hℓN f) := by
  intro m hm
  obtain ⟨x₁, y₁, hy₁, hxy₁⟩ := hf (m * ℓ) (coprime_mul_of_not_dvd hℓ hℓc hm)
  by_cases hdvd : ℓ ∣ m
  · obtain ⟨x₂, y₂, hy₂, hxy₂⟩ := hf (m / ℓ) (coprime_div_of_not_dvd hdvd hm)
    refine ⟨y₂ * x₁ + ℓ ^ (k - 1).toNat * (y₁ * x₂), y₁ * y₂,
      fun h => (h𝔪.isPrime.mem_or_mem h).elim hy₁ hy₂, ?_⟩
    push_cast
    rw [qCoeff_heckeTLin h𝔪 hℓ hℓN, hxy₁, hxy₂, if_pos hdvd,
      show ((ℓ : ℂ) ^ (k - 1) : ℂ) = ((ℓ : ℂ) ^ (k - 1).toNat : ℂ) from by
        rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]]
    ring
  · refine ⟨x₁, y₁, hy₁, ?_⟩
    rw [qCoeff_heckeTLin h𝔪 hℓ hℓN, if_neg hdvd, add_zero, hxy₁]

private theorem locZero_heckeT (hk1 : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N') (hℓc : ¬ ℓ ∣ c)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N') k} (hf : locInt c 𝔪 f) (hf0 : locZero c 𝔪 f) :
    locZero c 𝔪 (heckeTLin k hℓ hℓN f) := by
  intro m hm x y hy hxy
  rw [qCoeff_heckeTLin h𝔪 hℓ hℓN] at hxy
  obtain ⟨x₁, y₁, hy₁, hxy₁⟩ := hf (m * ℓ) (coprime_mul_of_not_dvd hℓ hℓc hm)
  by_cases hdvd : ℓ ∣ m
  · obtain ⟨x₂, y₂, hy₂, hxy₂⟩ := hf (m / ℓ) (coprime_div_of_not_dvd hdvd hm)
    rw [if_pos hdvd] at hxy
    have hkey : ((y₁ * y₂ * x : integralClosure ℤ ℂ) : ℂ) =
        ((y * (y₂ * x₁ + ℓ ^ (k - 1).toNat * (y₁ * x₂)) : integralClosure ℤ ℂ) : ℂ) := by
      push_cast
      rw [hxy, hxy₁, hxy₂,
        show ((ℓ : ℂ) ^ (k - 1) : ℂ) = ((ℓ : ℂ) ^ (k - 1).toNat : ℂ) from by
          rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]]
      ring
    have heq : y₁ * y₂ * x = y * (y₂ * x₁ + ℓ ^ (k - 1).toNat * (y₁ * x₂)) :=
      Subtype.coe_injective hkey
    have hmem : y * (y₂ * x₁ + ℓ ^ (k - 1).toNat * (y₁ * x₂)) ∈ 𝔪 :=
      𝔪.mul_mem_left y (𝔪.add_mem
        (𝔪.mul_mem_left y₂ (hf0 _ (coprime_mul_of_not_dvd hℓ hℓc hm) x₁ y₁ hy₁ hxy₁))
        (𝔪.mul_mem_left _ (𝔪.mul_mem_left y₁
          (hf0 _ (coprime_div_of_not_dvd hdvd hm) x₂ y₂ hy₂ hxy₂))))
    exact cancel h𝔪 hy₂ (cancel h𝔪 hy₁ (by rw [← mul_assoc, heq]; exact hmem))
  · rw [if_neg hdvd, add_zero] at hxy
    have hkey : ((y₁ * x : integralClosure ℤ ℂ) : ℂ) =
        ((y * x₁ : integralClosure ℤ ℂ) : ℂ) := by
      push_cast; rw [hxy, hxy₁]; ring
    exact cancel h𝔪 hy₁ ((Subtype.coe_injective hkey) ▸ 𝔪.mul_mem_left y
      (hf0 _ (coprime_mul_of_not_dvd hℓ hℓc hm) x₁ y₁ hy₁ hxy₁))

omit h𝔪 in

private theorem locInt_zsmul (z : ℤ) {f : CuspForm (CongruenceSubgroup.Gamma0 N') k}
    (hf : locInt c 𝔪 f) : locInt c 𝔪 (z • f) := by
  intro m hm
  obtain ⟨x, y, hy, hxy⟩ := hf m hm
  exact ⟨(z : integralClosure ℤ ℂ) * x, y, hy, by rw [qCoeff_zsmul]; push_cast; rw [hxy]; ring⟩

private theorem locZero_zsmul (z : ℤ) {f : CuspForm (CongruenceSubgroup.Gamma0 N') k}
    (hf : locInt c 𝔪 f) (hf0 : locZero c 𝔪 f) : locZero c 𝔪 (z • f) := by
  intro m hm x y hy hxy
  obtain ⟨x', y', hy', hxy'⟩ := hf m hm
  have hkey : ((y' * x : integralClosure ℤ ℂ) : ℂ) =
      ((y * ((z : integralClosure ℤ ℂ) * x') : integralClosure ℤ ℂ) : ℂ) := by
    push_cast; rw [hxy, qCoeff_zsmul, hxy']; ring
  exact cancel h𝔪 hy' ((Subtype.coe_injective hkey) ▸ 𝔪.mul_mem_left y
    (𝔪.mul_mem_left _ (hf0 m hm x' y' hy' hxy')))

end RC1.EntryAux

open RC1.EntryAux in
theorem solution (p : ℕ) [Fact p.Prime] (N' : ℕ) [NeZero N'] (k : ℤ) (S₀ : Set ℕ)
    (hS₀N : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S₀) (c : ℕ)
    (hc : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → ¬ ℓ ∣ c)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (G : CuspForm (CongruenceSubgroup.Gamma0 N') k)
    (hGint : ∀ n : ℕ, n.Coprime c → ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff G n)
    (hGne : ∃ (n : ℕ) (x y : integralClosure ℤ ℂ), n.Coprime c ∧ y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff G n ∧ x ∉ 𝔪)
    (a : ℕ → ℤ) (Q : ℕ → Prop)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
      ∃ e : integralClosure ℤ ℂ, (Q ℓ → e - (a ℓ : integralClosure ℤ ℂ) ∈ 𝔪) ∧
        ∀ (n : ℕ) (x x' y : integralClosure ℤ ℂ), n.Coprime c → y ∉ 𝔪 →
          (x : ℂ) = y * qCoeff (((heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra N' k S₀) :
              Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N') k)) G) n →
          (x' : ℂ) = y * qCoeff G n → x - e * x' ∈ 𝔪) :
    ∃ 𝔪ₖ : Ideal (heckeAlgebra N' k S₀), 𝔪ₖ.IsMaximal ∧
      (p : heckeAlgebra N' k S₀) ∈ 𝔪ₖ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'), Q ℓ →
        heckeAlgebra.T hℓ hℓN hℓS - ((a ℓ : ℤ) : heckeAlgebra N' k S₀) ∈ 𝔪ₖ := by

  by_cases hk1 : 1 ≤ k
  swap
  ·
    exfalso
    have hk0 : k ≤ 0 := Int.lt_add_one_iff.mp (not_le.mp hk1)
    have hG0 : (⇑G : UpperHalfPlane → ℂ) = 0 :=
      RC1.EntryAux.cuspForm_coe_eq_zero_of_nonpos_weight hk0 G
    obtain ⟨n, x, y, _, _, hxy, hx⟩ := hGne
    rw [show qCoeff G n = (0 : ℂ) from by
      unfold ModularFormClass.qCoeff; rw [hG0, UpperHalfPlane.qExpansion_zero]; simp,
      mul_zero] at hxy
    exact hx ((Subtype.coe_injective (a₂ := (0 : integralClosure ℤ ℂ))
      (by simpa using hxy)) ▸ 𝔪.zero_mem)

  open RC1.EntryAux in

  let P : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N') k) → Prop := fun T =>
    ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N') k, locInt c 𝔪 f →
      locInt c 𝔪 (T f) ∧ (locZero c 𝔪 f → locZero c 𝔪 (T f))

  have hP : ∀ T : heckeAlgebra N' k S₀, P (T : Module.End ℂ _) := by
    intro T
    have hT : (T : Module.End ℂ _) ∈ Algebra.adjoin ℤ (heckeGenerators N' k S₀) := T.2
    refine Algebra.adjoin_induction (p := fun T' _ => P T')
      (mem := ?_) (algebraMap := ?_) (add := ?_) (mul := ?_) hT
    ·
      rintro T' (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩)
      · intro f hf
        have hℓc : ¬ ℓ ∣ c := hc ℓ hℓ hℓS hℓN
        exact ⟨locInt_heckeT h𝔪 hk1 hℓ hℓN hℓc hf,
          fun hf0 => locZero_heckeT h𝔪 hk1 hℓ hℓN hℓc hf hf0⟩
      · exact absurd (hS₀N q hq hqN) hqS
    ·
      intro z f hf
      rw [show ((algebraMap ℤ (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N') k))) z) f
        = z • f from Module.End.intCast_apply z f]
      exact ⟨locInt_zsmul z hf, fun hf0 => locZero_zsmul h𝔪 z hf hf0⟩
    ·
      intro T₁ T₂ _ _ hT₁ hT₂ f hf
      have h1 := hT₁ f hf; have h2 := hT₂ f hf
      simp only [LinearMap.add_apply]
      exact ⟨locInt_add h𝔪 h1.1 h2.1,
        fun hf0 => locZero_add h𝔪 (h1.2 hf0) h1.1 (h2.2 hf0) h2.1⟩
    ·
      intro T₁ T₂ _ _ hT₁ hT₂ f hf
      have h2 := hT₂ f hf
      have h1 := hT₁ _ h2.1
      simp only [Module.End.mul_apply]
      exact ⟨h1.1, fun hf0 => h1.2 (h2.2 hf0)⟩

  have hGintP : locInt c 𝔪 G := hGint
  have hTG_int : ∀ T : heckeAlgebra N' k S₀,
      locInt c 𝔪 ((T : Module.End ℂ _) G) := fun T => (hP T G hGintP).1

  let 𝔪₀ : Ideal (heckeAlgebra N' k S₀) :=
    { carrier := {T | locZero c 𝔪 ((T : Module.End ℂ _) G)}
      add_mem' := by
        intro T₁ T₂ h₁ h₂
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, LinearMap.add_apply] at *
        exact locZero_add h𝔪 h₁ (hTG_int T₁) h₂ (hTG_int T₂)
      zero_mem' := by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_zero, LinearMap.zero_apply]
        exact locZero_zero
      smul_mem' := by
        intro S T hT
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, Module.End.mul_apply] at *
        exact (hP S _ (hTG_int T)).2 hT }

  have h𝔪₀_ne : 𝔪₀ ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one]
    intro h1
    have h1' : locZero c 𝔪 (((1 : heckeAlgebra N' k S₀) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N') k)) G) := h1
    simp only [Subalgebra.coe_one, Module.End.one_apply] at h1'
    obtain ⟨n, x, y, hn, hy, hxy, hx⟩ := hGne
    exact hx (h1' n hn x y hy hxy)

  have hp𝔪₀ : (p : heckeAlgebra N' k S₀) ∈ 𝔪₀ := by
    have hpact : (((p : heckeAlgebra N' k S₀) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N') k)) G) = (p : ℤ) • G := by
      rw [SubringClass.coe_natCast, Module.End.natCast_apply, ← natCast_zsmul]
    show locZero c 𝔪 _
    rw [hpact]
    intro m hm x y hy hxy
    obtain ⟨x', y', hy', hxy'⟩ := hGint m hm
    rw [qCoeff_zsmul] at hxy
    have hkey : ((y' * x : integralClosure ℤ ℂ) : ℂ) =
        ((y * ((p : integralClosure ℤ ℂ) * x') : integralClosure ℤ ℂ) : ℂ) := by
      push_cast; rw [hxy, hxy']; push_cast; ring
    exact cancel h𝔪 hy' ((Subtype.coe_injective hkey) ▸
      𝔪.mul_mem_left y (𝔪.mul_mem_right x' hp𝔪))

  have hTa𝔪₀ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'), Q ℓ →
      heckeAlgebra.T hℓ hℓN hℓS - ((a ℓ : ℤ) : heckeAlgebra N' k S₀) ∈ 𝔪₀ := by
    intro ℓ hℓ hℓS hℓN hQ
    obtain ⟨e, he_cong, he_rel⟩ := heig ℓ hℓ hℓS hℓN

    have hcoe1 : ((heckeAlgebra.T hℓ hℓN hℓS - ((a ℓ : ℤ) : heckeAlgebra N' k S₀) :
        heckeAlgebra N' k S₀) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N') k)) =
      ((heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra N' k S₀) : Module.End ℂ _) -
        ((a ℓ : ℤ) : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N') k)) := by
      rw [Subalgebra.coe_sub, SubringClass.coe_intCast]
    have hsub : (((heckeAlgebra.T hℓ hℓN hℓS - ((a ℓ : ℤ) : heckeAlgebra N' k S₀) :
        heckeAlgebra N' k S₀) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N') k)) G) =
        heckeTLin k hℓ hℓN G + (-(a ℓ) : ℤ) • G := by
      rw [hcoe1, LinearMap.sub_apply, heckeAlgebra.coe_T, Module.End.intCast_apply,
        sub_eq_add_neg, ← neg_smul]
    show locZero c 𝔪 _
    rw [hsub]
    intro m hm x y hy hxy
    rw [qCoeff_add, qCoeff_zsmul] at hxy
    obtain ⟨x', y', hy', hxy'⟩ := hGint m hm
    obtain ⟨xT, yT, hyT, hxyT⟩ := (locInt_heckeT h𝔪 hk1 hℓ hℓN (hc ℓ hℓ hℓS hℓN) hGintP) m hm

    have hyy : y' * yT ∉ 𝔪 := fun h => (h𝔪.isPrime.mem_or_mem h).elim hy' hyT
    have hrel : y' * xT - e * (yT * x') ∈ 𝔪 := by
      refine he_rel m (y' * xT) (yT * x') (y' * yT) hm hyy ?_ ?_
      · push_cast; rw [heckeAlgebra.coe_T, hxyT]; ring
      · push_cast; rw [hxy']; ring

    have hkey : ((y' * yT * x : integralClosure ℤ ℂ) : ℂ) =
        ((y * (y' * xT - (a ℓ : integralClosure ℤ ℂ) * (yT * x')) : integralClosure ℤ ℂ) : ℂ) := by
      push_cast
      rw [hxy, hxyT, hxy']
      push_cast
      ring
    have heq : y' * yT * x = y * (y' * xT - (a ℓ : integralClosure ℤ ℂ) * (yT * x')) :=
      Subtype.coe_injective hkey

    have hmem : y * (y' * xT - (a ℓ : integralClosure ℤ ℂ) * (yT * x')) ∈ 𝔪 := by
      have hrw : y' * xT - (a ℓ : integralClosure ℤ ℂ) * (yT * x') =
          (y' * xT - e * (yT * x')) + (e - (a ℓ : integralClosure ℤ ℂ)) * (yT * x') := by ring
      rw [hrw]
      exact 𝔪.mul_mem_left y (𝔪.add_mem hrel (𝔪.mul_mem_right _ (he_cong hQ)))
    exact cancel h𝔪 hyT (cancel h𝔪 hy' (by rw [← mul_assoc, heq]; exact hmem))

  obtain ⟨𝔪ₖ, h𝔪ₖ, hle⟩ := Ideal.exists_le_maximal 𝔪₀ h𝔪₀_ne
  exact ⟨𝔪ₖ, h𝔪ₖ, hle hp𝔪₀, fun ℓ hℓ hℓS hℓN hQ => hle (hTa𝔪₀ ℓ hℓ hℓS hℓN hQ)⟩

end S_CuspForm_heckeAlgebra_exists_isMaximal_heckeT_sub_mem_of_qCoeff_congr
end P2MW
export P2MW.S_CuspForm_heckeAlgebra_exists_isMaximal_heckeT_sub_mem_of_qCoeff_congr (solution)
