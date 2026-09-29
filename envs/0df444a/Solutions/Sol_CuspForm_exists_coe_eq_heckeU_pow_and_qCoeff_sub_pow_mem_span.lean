-- Prove2me | solution 1 for CuspForm.exists_coe_eq_heckeU_pow_and_qCoeff_sub_pow_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/fee79ef8-a53f-5495-ac35-d97987f16249

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import Theorems.Thm_ModularFormClass_qExpansion_heckeU_eq_heckeU
import Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_coe_eq_heckeU_pow_and_qCoeff_sub_pow_mem_span

set_option autoImplicit false

open UpperHalfPlane ModularFormClass
open scoped MatrixGroups ModularForm

namespace RC1

namespace FrobUAux

private lemma coeff_pow_prime_sub_pow_mem {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]
    (hpu : (p : R) ∈ nonunits R) (ψ : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff (p * n) (ψ ^ p) - (PowerSeries.coeff n ψ) ^ p ∈ Ideal.span {(p : R)} := by
  classical
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p hpu
  set P : Polynomial R := PowerSeries.trunc (p * n + 1) ψ with hP
  have hlt : p * n < p * n + 1 := Nat.lt_succ_self _
  have hn : n < p * n + 1 := Nat.lt_succ_of_le (Nat.le_mul_of_pos_left n hp.out.pos)

  have h1 : PowerSeries.coeff (p * n) (ψ ^ p) = (P ^ p).coeff (p * n) := by
    have := congrArg (fun Q : Polynomial R => Q.coeff (p * n)) (PowerSeries.trunc_trunc_pow ψ (p * n + 1) p)
    simp only [PowerSeries.coeff_trunc, if_pos hlt] at this
    rw [← this, ← hP, ← Polynomial.coe_pow, Polynomial.coeff_coe]
  have h2 : PowerSeries.coeff n ψ = P.coeff n := by
    rw [hP, PowerSeries.coeff_trunc, if_pos hn]
  rw [h1, h2, ← Ideal.Quotient.eq, map_pow]

  set Pb : Polynomial (R ⧸ Ideal.span {(p : R)}) := P.map (Ideal.Quotient.mk _) with hPb
  have key := congrArg (fun Q => Polynomial.coeff Q (n * p)) (Polynomial.map_frobenius_expand (p := p) Pb)
  simp only [Polynomial.coeff_map, Polynomial.coeff_expand_mul hp.out.pos, frobenius_def] at key
  rw [mul_comm p n, ← Polynomial.coeff_map, Polynomial.map_pow, ← hPb, ← key, hPb, Polynomial.coeff_map]

private lemma natCast_mem_nonunits (p : ℕ) [hp : Fact p.Prime] :
    ((p : integralClosure ℤ ℂ) : integralClosure ℤ ℂ) ∈ nonunits (integralClosure ℤ ℂ) := by
  rw [mem_nonunits_iff]
  rintro ⟨u, hu⟩

  have hinv : ((↑(u⁻¹ : (integralClosure ℤ ℂ)ˣ) : integralClosure ℤ ℂ) : ℂ) = (p : ℂ)⁻¹ := by
    have h1 : ((↑(u⁻¹ : (integralClosure ℤ ℂ)ˣ) : integralClosure ℤ ℂ) : ℂ) * (p : ℂ) = 1 := by
      have := congrArg (fun x : integralClosure ℤ ℂ => (x : ℂ)) (u.inv_mul)
      rw [hu] at this
      simpa using this
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    exact (eq_inv_of_mul_eq_one_left h1)
  have hint : IsIntegral ℤ ((p : ℂ)⁻¹) := hinv ▸ (↑(u⁻¹ : (integralClosure ℤ ℂ)ˣ) : integralClosure ℤ ℂ).2
  have hintQ : IsIntegral ℤ ((p : ℚ)⁻¹) := by
    have : algebraMap ℚ ℂ ((p : ℚ)⁻¹) = (p : ℂ)⁻¹ := by simp
    rw [← this, isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective] at hint
    exact hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintQ
  have hyp : (y : ℚ) * p = 1 := by
    rw [eq_intCast] at hy
    rw [hy, inv_mul_cancel₀]
    exact_mod_cast hp.out.ne_zero
  have hyp' : y * p = 1 := by exact_mod_cast hyp
  have : (p : ℤ) = 1 := Int.eq_one_of_mul_eq_one_left (by positivity) hyp'
  exact hp.out.one_lt.ne' (by exact_mod_cast this)

end FrobUAux

end RC1

open RC1 in
open RC1.FrobUAux in
theorem solution (p : ℕ) [Fact p.Prime] {M : ℕ} [NeZero M] (hpM : p ^ 2 ∣ M) (k : ℤ)
    (g : CuspForm (CongruenceSubgroup.Gamma0 M) k)
    (hgint : ∀ n : ℕ, ∃ a : integralClosure ℤ ℂ, (a : ℂ) = qCoeff g n) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma0 (M / p)) (p * k),
      ⇑F = ModularForm.heckeU (p * k) p ((⇑g) ^ p) ∧
      (∀ n : ℕ, ∃ A : integralClosure ℤ ℂ, (A : ℂ) = qCoeff F n) ∧
      (∀ K : IntermediateField ℚ ℂ, (∀ n : ℕ, qCoeff g n ∈ K) → ∀ n : ℕ, qCoeff F n ∈ K) ∧
      (∀ (n : ℕ) (a A : integralClosure ℤ ℂ), (a : ℂ) = qCoeff g n → (A : ℂ) = qCoeff F n →
        A - a ^ p ∈ Ideal.span {(p : integralClosure ℤ ℂ)}) := by
  classical
  have hp1 : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp1.ne_zero
  have hM0 : M ≠ 0 := NeZero.ne M
  haveI : NeZero (M / p) := ⟨by
    intro h
    rcases hpM with ⟨c, hc⟩
    have : p ≤ M / p := by
      rw [hc, pow_two, mul_assoc, Nat.mul_div_cancel_left _ hp1.pos]
      rcases Nat.eq_zero_or_pos c with rfl | hcpos
      · simp [hc] at hM0
      · exact Nat.le_mul_of_pos_right p hcpos
    omega⟩
  have h1M : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp

  let gM : ModularForm (CongruenceSubgroup.Gamma0 M) k := (g : ModularForm (CongruenceSubgroup.Gamma0 M) k)
  have hgM : (⇑gM : UpperHalfPlane → ℂ) = ⇑g := rfl
  have hw : k + ((p - 1 : ℕ) : ℤ) * k = (p : ℤ) * k := by
    rw [Nat.cast_sub hp1.one_le]; push_cast; ring
  let Gc : CuspForm (CongruenceSubgroup.Gamma0 M) (p * k) := CuspForm.mcast hw (g.mulModularForm (gM.pow (p - 1)))
  have hGc : (⇑Gc : UpperHalfPlane → ℂ) = (⇑g) ^ p := by
    show ⇑g * ⇑(gM.pow (p - 1)) = (⇑g) ^ p
    rw [ModularForm.coe_pow, hgM, ← pow_succ', Nat.sub_add_cancel hp1.one_le]

  have hinvM : ∀ γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)),
      SlashAction.map ((p : ℤ) * k) γ ((⇑g) ^ p) = (⇑g) ^ p := fun γ hγ => by
    rw [← hGc]; exact SlashInvariantForm.slash_action_eqn Gc γ hγ
  have hinv : ∀ γ ∈ (CongruenceSubgroup.Gamma0 (M / p) : Subgroup (GL (Fin 2) ℝ)),
      SlashAction.map ((p : ℤ) * k) γ (ModularForm.heckeU ((p : ℤ) * k) p ((⇑g) ^ p)) =
        ModularForm.heckeU ((p : ℤ) * k) p ((⇑g) ^ p) :=
    fun γ hγ => ModularForm.heckeU_slash_eq_self_of_mem_Gamma0_div ((p : ℤ) * k) hpM hinvM γ hγ
  have hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (ModularForm.heckeU ((p : ℤ) * k) p ((⇑g) ^ p)) := by
    have := ModularForm.mdifferentiable_heckeU Gc.holo' ((p : ℤ) * k) p
    rwa [show ((Gc.toSlashInvariantForm : UpperHalfPlane → ℂ)) = (⇑g) ^ p from hGc] at this
  have hzero : ∀ c : OnePoint ℝ, IsCusp c (CongruenceSubgroup.Gamma0 (M / p) : Subgroup (GL (Fin 2) ℝ)) →
      OnePoint.IsZeroAt c (ModularForm.heckeU ((p : ℤ) * k) p ((⇑g) ^ p)) ((p : ℤ) * k) := fun c hc => by
    have hc' : IsCusp c (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) :=
      (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)
    rw [← hGc]
    exact CuspFormClass.isZeroAt_heckeU Gc p hc'
  let F : CuspForm (CongruenceSubgroup.Gamma0 (M / p)) (p * k) :=
    { toFun := ModularForm.heckeU ((p : ℤ) * k) p ((⇑g) ^ p)
      slash_action_eq' := hinv
      holo' := hhol
      zero_at_cusps' := fun hc => hzero _ hc }
  have hF : (⇑F : UpperHalfPlane → ℂ) = ModularForm.heckeU ((p : ℤ) * k) p ((⇑g) ^ p) := rfl

  have hGq : qExpansion 1 (⇑Gc) = (qExpansion 1 ⇑g) ^ p := by
    rw [hGc, show ((⇑g) ^ p : UpperHalfPlane → ℂ) = ⇑(gM.pow p) by rw [ModularForm.coe_pow, hgM],
      ModularForm.qExpansion_pow one_pos h1M gM p, hgM]
  have hFq : ∀ n : ℕ, qCoeff (⇑F) n = PowerSeries.coeff (p * n) ((qExpansion 1 ⇑g) ^ p) := by
    intro n
    show PowerSeries.coeff n (qExpansion 1 ⇑F) = _
    rw [hF, ← hGc, ModularFormClass.qExpansion_heckeU_eq_heckeU Gc h1M hp0, PowerSeries.coeff_heckeU, hGq]

  let ψ : PowerSeries (integralClosure ℤ ℂ) := PowerSeries.mk fun n => (hgint n).choose
  have hψ : ∀ n, ((PowerSeries.coeff n ψ : integralClosure ℤ ℂ) : ℂ) = qCoeff (⇑g) n := fun n => by
    simp only [ψ, PowerSeries.coeff_mk]; exact (hgint n).choose_spec
  have hψmap : ψ.map (algebraMap (integralClosure ℤ ℂ) ℂ) = qExpansion 1 ⇑g := by
    ext n; rw [PowerSeries.coeff_map]; exact hψ n
  have hFψ : ∀ n : ℕ, qCoeff (⇑F) n = ((PowerSeries.coeff (p * n) (ψ ^ p) : integralClosure ℤ ℂ) : ℂ) := by
    intro n
    rw [hFq, ← hψmap, ← map_pow, PowerSeries.coeff_map]; rfl
  refine ⟨F, hF, fun n => ⟨_, (hFψ n).symm⟩, ?_, ?_⟩
  ·
    intro K hK n
    let ψK : PowerSeries K := PowerSeries.mk fun n => (⟨qCoeff (⇑g) n, hK n⟩ : K)
    have hψK : ψK.map (algebraMap K ℂ) = qExpansion 1 ⇑g := by
      ext m; rw [PowerSeries.coeff_map]; simp only [ψK, PowerSeries.coeff_mk]; rfl
    rw [hFq, ← hψK, ← map_pow, PowerSeries.coeff_map]
    exact (PowerSeries.coeff (p * n) (ψK ^ p)).2
  ·
    intro n a A ha hA
    have hinj : Function.Injective (fun x : integralClosure ℤ ℂ => (x : ℂ)) := Subtype.coe_injective
    have ha' : a = PowerSeries.coeff n ψ := hinj (by simp only [ha, hψ])
    have hA' : A = PowerSeries.coeff (p * n) (ψ ^ p) := hinj (by simp only [hA, hFψ])
    rw [ha', hA']
    exact coeff_pow_prime_sub_pow_mem p (natCast_mem_nonunits p) ψ n

end S_CuspForm_exists_coe_eq_heckeU_pow_and_qCoeff_sub_pow_mem_span
end P2MW
export P2MW.S_CuspForm_exists_coe_eq_heckeU_pow_and_qCoeff_sub_pow_mem_span (solution)
