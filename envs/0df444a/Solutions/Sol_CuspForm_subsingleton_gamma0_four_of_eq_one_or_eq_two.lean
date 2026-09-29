-- Prove2me | solution 1 for CuspForm.subsingleton_gamma0_four_of_eq_one_or_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7f6c05f6-5a87-5b8f-86a5-7d802bec7a80

import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_subsingleton_gamma0_four_of_eq_one_or_eq_two

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Matrix.SpecialLinearGroup SlashInvariantForm CongruenceSubgroup
open scoped MatrixGroups ModularForm Topology

namespace RC2rCosets

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

local notation "𝒬" => 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)

section generic

open scoped Classical

variable [SlashInvariantFormClass F 𝒢 k] [𝒢.IsFiniteRelIndex 𝒮ℒ]

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
lemma quotientFunc_coe (f : F) (h : 𝒮ℒ) :
    quotientFunc f (h : 𝒬) = (f : ℍ → ℂ) ∣[k] h.val⁻¹ := rfl

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in

lemma smul_coe_one_eq {g : 𝒮ℒ} (hg : (g : GL (Fin 2) ℝ) ∈ 𝒢) : g • ((1 : 𝒮ℒ) : 𝒬) = (1 : 𝒮ℒ) := by
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
  exact QuotientGroup.eq.mpr (by simpa [Subgroup.mem_subgroupOf] using inv_mem hg)

variable (𝒢) in

def normCompl (f : F) : ℍ → ℂ :=
  letI := Fintype.ofFinite 𝒬
  ∏ q ∈ Finset.univ.erase ((1 : 𝒮ℒ) : 𝒬), quotientFunc f q

lemma card_univ_erase_one :
    letI := Fintype.ofFinite 𝒬
    (Finset.univ.erase ((1 : 𝒮ℒ) : 𝒬)).card = Nat.card 𝒬 - 1 := by
  letI := Fintype.ofFinite 𝒬
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Nat.card_eq_fintype_card]

theorem coe_norm_eq_mul_normCompl [ModularFormClass F 𝒢 k] (f : F) :
    ⇑(ModularForm.norm 𝒮ℒ f) = (f : ℍ → ℂ) * normCompl 𝒢 f := by
  letI := Fintype.ofFinite 𝒬
  simp only [ModularForm.coe_norm, normCompl]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ((1 : 𝒮ℒ) : 𝒬)), quotientFunc_coe]
  simp

theorem normCompl_slash (h𝒢 : 𝒢 ≤ 𝒮ℒ) (f : F) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ 𝒢) :
    normCompl 𝒢 f ∣[k * ((Nat.card 𝒬 - 1 : ℕ) : ℤ)] γ = normCompl 𝒢 f := by
  letI := Fintype.ofFinite 𝒬
  have hγ' : γ ∈ 𝒮ℒ := h𝒢 hγ
  rw [← card_univ_erase_one, normCompl, ModularForm.prod_slash,
    Subgroup.HasDetPlusMinusOne.abs_det hγ', one_zpow, one_smul]
  simp_rw [quotientFunc_smul f hγ']
  have := Equiv.Perm.prod_comp (MulAction.toPerm (⟨γ, hγ'⟩⁻¹ : 𝒮ℒ))
    (Finset.univ.erase ((1 : 𝒮ℒ) : 𝒬)) (quotientFunc f) (fun q hq => by
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_diff, Set.mem_univ, true_and,
        Set.mem_singleton_iff]
      rintro rfl
      apply hq
      rw [MulAction.toPerm_apply]
      exact smul_coe_one_eq (by simpa using inv_mem hγ))
  simpa only [MulAction.toPerm_apply] using this

def normComplForm [𝒢.IsArithmetic] [ModularFormClass F 𝒢 k] (h𝒢 : 𝒢 ≤ 𝒮ℒ) (f : F) :
    ModularForm 𝒢 (k * ((Nat.card 𝒬 - 1 : ℕ) : ℤ)) where
  toFun := normCompl 𝒢 f
  slash_action_eq' γ hγ := normCompl_slash h𝒢 f hγ
  holo' := by
    letI := Fintype.ofFinite 𝒬
    simp only [normCompl]
    exact .prod fun q _ => Quotient.inductionOn q fun r => (ModularForm.translate f r.val⁻¹).holo'
  bdd_at_cusps' h γ := by
    rintro rfl
    letI := Fintype.ofFinite 𝒬
    simp_rw [normCompl, IsBoundedAtImInfty, Filter.BoundedAtFilter]
    rw [← card_univ_erase_one (𝒢 := 𝒢), ModularForm.prod_slash]
    apply Asymptotics.IsBigO.const_smul_left
    rw [show (1 : ℍ → ℝ) = (fun x ↦ ∏ i ∈ Finset.univ.erase ((1 : 𝒮ℒ) : 𝒬), 1) by ext; simp,
      Finset.prod_fn]
    refine .finsetProd fun q _ => Quotient.inductionOn q fun r =>
      (ModularForm.translate f _).bdd_at_cusps' ?_ γ rfl
    simpa using ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z 𝒢).mp h).of_isFiniteRelIndex_conj
      (𝒢 := 𝒢) r.prop

@[scoped simp] lemma coe_normComplForm [𝒢.IsArithmetic] [ModularFormClass F 𝒢 k] (h𝒢 : 𝒢 ≤ 𝒮ℒ) (f : F) :
    ⇑(normComplForm h𝒢 f) = normCompl 𝒢 f := rfl

theorem isZeroAtImInfty_normCompl [𝒢.IsArithmetic] [CuspFormClass F 𝒢 k] (f : F)
    (hcard : 1 < Nat.card 𝒬) : IsZeroAtImInfty (normCompl 𝒢 f) := by
  letI := Fintype.ofFinite 𝒬
  set s := Finset.univ.erase ((1 : 𝒮ℒ) : 𝒬) with hs
  have hne : s.Nonempty := by
    rw [← Finset.card_pos, hs, card_univ_erase_one]
    omega
  obtain ⟨q₀, hq₀⟩ := hne
  have hfac : ∀ q : 𝒬, IsZeroAtImInfty (quotientFunc f q) := fun q =>
    Quotient.inductionOn q fun r => by
      obtain ⟨γ, hγ⟩ := r.prop
      change IsZeroAtImInfty ((f : ℍ → ℂ) ∣[k] r.val⁻¹)
      rw [← hγ, ← map_inv]
      exact CuspFormClass.zero_at_infty_slash f γ⁻¹
  have h0 : Filter.Tendsto (fun x => ∏ q ∈ s, quotientFunc f q x) atImInfty
      (𝓝 (∏ q ∈ s, (fun _ => (0 : ℂ)) q)) :=
    tendsto_finsetProd s fun q _ => hfac q
  rw [Finset.prod_eq_zero hq₀ rfl] at h0
  have : normCompl 𝒢 f = fun x => ∏ q ∈ s, quotientFunc f q x := by
    ext x; simp [normCompl, hs, Finset.prod_apply]
  rw [this]
  exact h0

end generic

section Gamma0

lemma T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ Gamma0 N := by
  simp [Gamma0_mem, ModularGroup.coe_T]

lemma S_notMem_Gamma0_two : ModularGroup.S ∉ Gamma0 2 := by
  simp [Gamma0_mem, ModularGroup.coe_S]

lemma Gamma0_le_SL (N : ℕ) : ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

lemma one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma0 N)]
  exact AddSubgroup.mem_zmultiples 1

def slq (Γ : Subgroup SL(2, ℤ)) (γ : SL(2, ℤ)) :
    𝒮ℒ ⧸ ((Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :=
  ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ).rangeRestrict γ : 𝒮ℒ)

lemma slq_surjective (Γ : Subgroup SL(2, ℤ)) : Function.Surjective (slq Γ) := by
  intro q
  induction q using Quotient.inductionOn with
  | h r =>
    obtain ⟨γ, hγ⟩ := (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ).rangeRestrict_surjective r
    exact ⟨γ, by rw [slq, hγ]⟩

lemma slq_eq_slq_iff (Γ : Subgroup SL(2, ℤ)) (ρ γ : SL(2, ℤ)) :
    slq Γ ρ = slq Γ γ ↔ ρ⁻¹ * γ ∈ Γ := by
  rw [slq, slq, QuotientGroup.eq, Subgroup.mem_subgroupOf, ← map_inv, ← map_mul,
    MonoidHom.coe_rangeRestrict]
  exact Subgroup.mem_map_iff_mem mapGL_injective

lemma S_mul_apply_one_zero (γ : SL(2, ℤ)) :
    (↑(ModularGroup.S * γ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (↑γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]

lemma ST_mul_apply_one_zero (γ : SL(2, ℤ)) :
    (↑(ModularGroup.S * ModularGroup.T * γ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
      (↑γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (↑γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T, Matrix.mul_apply,
    Fin.sum_univ_two]

def rep : Fin 3 → SL(2, ℤ) := ![1, ModularGroup.S⁻¹, (ModularGroup.S * ModularGroup.T)⁻¹]

lemma slq_rep_surjective : Function.Surjective (fun i => slq (Gamma0 2) (rep i)) := by
  intro q
  obtain ⟨γ, rfl⟩ := slq_surjective (Gamma0 2) q
  have key : ∀ a c : ZMod 2, c = 0 ∨ a = 0 ∨ a + c = 0 := by decide
  rcases key ((↑γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) ((↑γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    with hc | ha | hac
  · refine ⟨0, (slq_eq_slq_iff _ _ _).mpr ?_⟩
    simpa [rep, Gamma0_mem] using hc
  · refine ⟨1, (slq_eq_slq_iff _ _ _).mpr ?_⟩
    rw [rep, Matrix.cons_val_one, Matrix.cons_val_zero, inv_inv, Gamma0_mem, S_mul_apply_one_zero]
    exact ha
  · refine ⟨2, (slq_eq_slq_iff _ _ _).mpr ?_⟩
    rw [show rep 2 = (ModularGroup.S * ModularGroup.T)⁻¹ from rfl, inv_inv, Gamma0_mem,
      ST_mul_apply_one_zero, Int.cast_add]
    exact hac

theorem card_quotient_Gamma0_two_le :
    Nat.card (𝒮ℒ ⧸ (((Gamma0 2 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)) ≤ 3 := by
  simpa using Nat.card_le_card_of_surjective _ slq_rep_surjective

theorem one_lt_card_quotient_Gamma0_two :
    1 < Nat.card (𝒮ℒ ⧸ (((Gamma0 2 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)) := by
  rw [Finite.one_lt_card_iff_nontrivial]
  refine ⟨⟨slq (Gamma0 2) 1, slq (Gamma0 2) ModularGroup.S, fun h => S_notMem_Gamma0_two ?_⟩⟩
  simpa using (slq_eq_slq_iff _ _ _).mp h

end Gamma0

section WL1A

p2m_open "ModularForm CuspForm ModularForm.CuspForm Complex Matrix ModularGroup"
open scoped Manifold

lemma gamma0_one_eq_top : Gamma0 1 = (⊤ : Subgroup SL(2, ℤ)) := by
  ext A
  simpa [Gamma0_mem] using Subsingleton.elim _ _

lemma coe_gamma0_one :
    (Subgroup.map (mapGL ℝ) (Gamma0 1) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [gamma0_one_eq_top, ← MonoidHom.range_eq_map]

lemma arm_one : Subsingleton (CuspForm (Gamma0 1) (4 : ℤ)) := by
  rw [show Subgroup.map (mapGL ℝ) (Gamma0 1) = 𝒮ℒ from coe_gamma0_one]
  exact rank_zero_iff.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))

variable (f : CuspForm (Gamma0 2) (4 : ℤ))

local notation "g₂" => normComplForm (𝒢 := Subgroup.map (mapGL ℝ) (Gamma0 2)) (Gamma0_le_SL 2) f

lemma analyticAt_cuspFunction_f : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods_Gamma0 2)

lemma analyticAt_cuspFunction_gFn :
    AnalyticAt ℂ (cuspFunction 1 (normCompl (k := (4 : ℤ)) (Subgroup.map (mapGL ℝ) (Gamma0 2)) f)) 0 := by
  rw [← coe_normComplForm (Gamma0_le_SL 2) f]
  exact ModularFormClass.analyticAt_cuspFunction_zero g₂ one_pos (one_mem_strictPeriods_Gamma0 2)

lemma order_pos_f : 1 ≤ (qExpansion 1 (⇑f)).order := by
  refine le_trans (by norm_num) (PowerSeries.nat_le_order _ 1 fun i hi => ?_)
  have h0 : i = 0 := by omega
  subst h0
  exact CuspFormClass.qExpansion_coeff_zero f one_pos (one_mem_strictPeriods_Gamma0 2)

lemma order_pos_gFn :
    1 ≤ (qExpansion 1 (normCompl (k := (4 : ℤ)) (Subgroup.map (mapGL ℝ) (Gamma0 2)) f)).order := by
  refine le_trans (by norm_num) (PowerSeries.nat_le_order _ 1 fun i hi => ?_)
  have h0 : i = 0 := by omega
  subst h0
  rw [qExpansion_coeff]
  simp [(isZeroAtImInfty_normCompl f one_lt_card_quotient_Gamma0_two).cuspFunction_apply_zero
    one_pos]

lemma order_qExpansion_norm :
    (1 : ℕ∞) < (qExpansion 1 ⇑(ModularForm.norm 𝒮ℒ f)).order := by
  rw [coe_norm_eq_mul_normCompl f,
    qExpansion_mul (analyticAt_cuspFunction_f f) (analyticAt_cuspFunction_gFn f),
    PowerSeries.order_mul]
  calc (1 : ℕ∞) < 1 + 1 := by norm_num
  _ ≤ (qExpansion 1 ⇑f).order +
      (qExpansion 1 (normCompl (k := (4 : ℤ)) (Subgroup.map (mapGL ℝ) (Gamma0 2)) f)).order :=
    add_le_add (order_pos_f f) (order_pos_gFn f)

lemma f_eq_zero : f = 0 := by
  have hF : ModularForm.norm 𝒮ℒ f = 0 := by
    apply ModularForm.sturm_bound_levelOne
    refine lt_of_le_of_lt ?_ (order_qExpansion_norm f)
    have h3 := card_quotient_Gamma0_two_le
    have hle : ((4 : ℤ) *
        Nat.card (↥𝒮ℒ ⧸ (((Gamma0 2 : Subgroup SL(2,ℤ)).map (mapGL ℝ)).subgroupOf 𝒮ℒ))).toNat
        / 12 ≤ 1 := by omega
    exact_mod_cast Nat.cast_le.mpr hle
  have hcoe : (⇑f : ℍ → ℂ) = 0 := (ModularForm.norm_eq_zero_iff 𝒮ℒ f).mp hF
  ext τ
  exact congrFun hcoe τ

end WL1A

end RC2rCosets
p2m_reactivate "P2MW.S_CuspForm_subsingleton_gamma0_four_of_eq_one_or_eq_two.RC2rCosets"

end
p2m_reactivate "P2MW.S_CuspForm_subsingleton_gamma0_four_of_eq_one_or_eq_two.RC2rCosets"

theorem solution (N' : ℕ) (hN' : N' = 1 ∨ N' = 2) :
    Subsingleton (CuspForm (CongruenceSubgroup.Gamma0 N') (4 : ℤ)) := by
  rcases hN' with rfl | rfl
  · exact RC2rCosets.arm_one
  · exact ⟨fun a b => by rw [RC2rCosets.f_eq_zero a, RC2rCosets.f_eq_zero b]⟩

end S_CuspForm_subsingleton_gamma0_four_of_eq_one_or_eq_two
end P2MW
export P2MW.S_CuspForm_subsingleton_gamma0_four_of_eq_one_or_eq_two (solution)
