-- Prove2me | solution 1 for CuspForm.linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/edd6a9b8-48a5-5957-ac63-dc4fc32fdf7b

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import Theorems.Thm_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul
import Theorems.Thm_CuspForm_exists_degeneracy_gamma1_hasNebentypus
import Theorems.Thm_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false

noncomputable section

namespace CuspForm
p2m_export "CuspForm" "IsGLPos.coe_smul coe_smul coe_add HasNebentypus IsEigenformWith diamondLinOne heckeTLinOne coe_heckeTLinOne_apply exists_degeneracy_gamma1_hasNebentypus HasNebentypus.diamondLinOne_apply_eq_smul"
namespace M4aIndep
p2m_open "CuspForm"

open CongruenceSubgroup
open scoped MatrixGroups ModularForm

section Separation

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*} {n : ℕ}

private theorem eq_zero_of_sum_eq_zero_of_eigen (T : ι → V →ₗ[ℂ] V) (χ : Fin n → ι → ℂ)
    (hsep : ∀ i j : Fin n, i ≠ j → ∃ a : ι, χ i a ≠ χ j a) :
    ∀ (s : Finset (Fin n)) (w : Fin n → V),
      (∀ i ∈ s, ∀ a : ι, T a (w i) = χ i a • w i) → (∑ i ∈ s, w i) = 0 → ∀ i ∈ s, w i = 0 := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro w hw hsum i₀ hi₀
    by_cases hcard : ∀ j ∈ s, j = i₀
    ·
      have hs : s = {i₀} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hi₀, hcard⟩
      rw [hs, Finset.sum_singleton] at hsum
      exact hsum
    · push Not at hcard
      obtain ⟨j₀, hj₀, hji⟩ := hcard
      obtain ⟨a, ha⟩ := hsep i₀ j₀ (Ne.symm hji)

      let w' : Fin n → V := fun i => (χ i a - χ j₀ a) • w i
      have hw' : ∀ i ∈ s.erase j₀, ∀ b : ι, T b (w' i) = χ i b • w' i := by
        intro i hi b
        show T b ((χ i a - χ j₀ a) • w i) = χ i b • ((χ i a - χ j₀ a) • w i)
        rw [map_smul, hw i (Finset.mem_of_mem_erase hi) b, smul_comm]
      have hsum' : (∑ i ∈ s.erase j₀, w' i) = 0 := by
        have h1 : (∑ i ∈ s, w' i) = T a (∑ i ∈ s, w i) - χ j₀ a • ∑ i ∈ s, w i := by
          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i hi => ?_
          show (χ i a - χ j₀ a) • w i = T a (w i) - χ j₀ a • w i
          rw [hw i hi a, sub_smul]
        have h2 : w' j₀ = 0 := by show (χ j₀ a - χ j₀ a) • w j₀ = 0; rw [sub_self, zero_smul]
        rw [← Finset.sum_erase_add _ _ hj₀, h2, add_zero] at h1
        rw [h1, hsum, map_zero, smul_zero, sub_zero]
      have h := ih (s.erase j₀) (Finset.erase_ssubset hj₀) w' hw' hsum' i₀
        (Finset.mem_erase.mpr ⟨Ne.symm hji, hi₀⟩)

      exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr ha)

end Separation

section QCoeff

variable {M : ℕ} {k : ℤ}

private theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

private theorem qCoeff_add (f g : CuspForm (Gamma1 M) k) (m : ℕ) :
    ModularFormClass.qCoeff (⇑(f + g)) m = ModularFormClass.qCoeff f m + ModularFormClass.qCoeff g m := by
  unfold ModularFormClass.qCoeff
  rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g]
  simp

private theorem qCoeff_smul (c : ℂ) (f : CuspForm (Gamma1 M) k) (m : ℕ) :
    ModularFormClass.qCoeff (⇑(c • f)) m = c * ModularFormClass.qCoeff f m := by
  unfold ModularFormClass.qCoeff
  rw [CuspForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c f]
  simp

private theorem qCoeff_zero_form (m : ℕ) : ModularFormClass.qCoeff (⇑(0 : CuspForm (Gamma1 M) k)) m = 0 := by
  have h := qCoeff_smul (0 : ℂ) (0 : CuspForm (Gamma1 M) k) m
  simpa using h

private theorem qCoeff_sum {α : Type*} (s : Finset α) (F : α → CuspForm (Gamma1 M) k) (m : ℕ) :
    ModularFormClass.qCoeff (⇑(∑ i ∈ s, F i)) m = ∑ i ∈ s, ModularFormClass.qCoeff (F i) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using qCoeff_zero_form (M := M) (k := k) m
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, qCoeff_add, ih]

end QCoeff

private theorem main
    (M : ℕ) [NeZero M] (k : ℤ) (n : ℕ) (L : Fin n → ℕ) [∀ i, NeZero (L i)] (hL : ∀ i, L i ∣ M)
    (ε : (i : Fin n) → DirichletCharacter ℂ (L i))
    (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
    (hg : ∀ i, CuspForm.IsEigenformWith (ε i) (g i))
    (hsep : ∀ i j : Fin n, i ≠ j → ∃ p : ℕ, p.Prime ∧ ¬ p ∣ M ∧
      ModularFormClass.qCoeff (g i) p ≠ ModularFormClass.qCoeff (g j) p)
    (G : Fin n → ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hG : ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
      ∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ))
    (c : Fin n → ℕ → ℂ)
    (hc : (∑ i, ∑ d ∈ Nat.divisors (M / L i), c i d • G i d) = 0) :
    ∀ (i : Fin n), ∀ d ∈ Nat.divisors (M / L i), c i d = 0 := by
  classical

  have hGfacts : ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
      (∀ m : ℕ, ModularFormClass.qCoeff (⇑(G i d)) m =
        if d ∣ m then ModularFormClass.qCoeff (⇑(g i)) (m / d) else 0) ∧
      CuspForm.HasNebentypus (DirichletCharacter.changeLevel (hL i) (ε i)) (G i d) := by
    intro i d hd
    have hdM : L i * d ∣ M := Nat.mul_dvd_of_dvd_div (hL i) hd
    obtain ⟨G', hG'τ, hG'coeff, hG'neb⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) hdM (g i)
    have hGG : G i d = G' :=
      DFunLike.coe_injective (funext fun τ => (hG i d hd τ).trans (hG'τ τ).symm)
    rw [hGG]
    exact ⟨hG'coeff, hG'neb (ε i) (hg i).hasNebentypus⟩

  have hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (i : Fin n) (d : ℕ), d ∣ M / L i →
      CuspForm.heckeTLinOne k hℓ hℓM (G i d) = ModularFormClass.qCoeff (g i) ℓ • G i d := by
    intro ℓ hℓ hℓM i d hd
    have hcop : Nat.Coprime ℓ M := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM
    have hdia : CuspForm.diamondLinOne M k ℓ (G i d) =
        DirichletCharacter.changeLevel (hL i) (ε i) (ℓ : ZMod M) • G i d :=
      (hGfacts i d hd).2.diamondLinOne_apply_eq_smul hcop
    have heval : DirichletCharacter.changeLevel (hL i) (ε i) (ℓ : ZMod M) = ε i (ℓ : ZMod (L i)) := by
      have hu : ((ZMod.unitOfCoprime ℓ hcop : (ZMod M)ˣ) : ZMod M) = (ℓ : ZMod M) :=
        ZMod.coe_unitOfCoprime ℓ hcop
      rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd (ε i) (hL i), hu, ZMod.cast_natCast (hL i)]
    refine DFunLike.coe_injective ?_
    show ⇑(CuspForm.heckeTLinOne k hℓ hℓM (G i d)) = ⇑(ModularFormClass.qCoeff (g i) ℓ • G i d)
    rw [CuspForm.coe_heckeTLinOne_apply, hdia, heval, CuspForm.IsGLPos.coe_smul, CuspForm.IsGLPos.coe_smul,
      ModularForm.smul_slash]
    have hσ : (UpperHalfPlane.σ (ModularForm.heckeDiagMatrix ℓ)) (ε i (ℓ : ZMod (L i))) = ε i (ℓ : ZMod (L i)) := by
      rw [ModularForm.σ_heckeDiagMatrix]; rfl
    rw [hσ]
    exact (hg i).heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul M k (hL i) (G i) (hG i)
      hℓ hℓM hd

  set Φ : Fin n → CuspForm (CongruenceSubgroup.Gamma1 M) k :=
    fun i => ∑ d ∈ Nat.divisors (M / L i), c i d • G i d with hΦ
  have hΦT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (i : Fin n),
      CuspForm.heckeTLinOne k hℓ hℓM (Φ i) = ModularFormClass.qCoeff (g i) ℓ • Φ i := by
    intro ℓ hℓ hℓM i
    show CuspForm.heckeTLinOne k hℓ hℓM (∑ d ∈ Nat.divisors (M / L i), c i d • G i d) =
      ModularFormClass.qCoeff (g i) ℓ • ∑ d ∈ Nat.divisors (M / L i), c i d • G i d
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [map_smul, hT ℓ hℓ hℓM i d (Nat.mem_divisors.mp hd).1, smul_comm]

  have hΦ0 : ∀ i, Φ i = 0 := by
    let ι := {p : ℕ // p.Prime ∧ ¬ p ∣ M}
    let T : ι → CuspForm (CongruenceSubgroup.Gamma1 M) k →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma1 M) k :=
      fun a => CuspForm.heckeTLinOne k a.2.1 a.2.2
    let χ : Fin n → ι → ℂ := fun i a => ModularFormClass.qCoeff (g i) a.1
    have hsep' : ∀ i j : Fin n, i ≠ j → ∃ a : ι, χ i a ≠ χ j a := by
      intro i j hij
      obtain ⟨p, hp, hpM, hne⟩ := hsep i j hij
      exact ⟨⟨p, hp, hpM⟩, hne⟩
    have h := eq_zero_of_sum_eq_zero_of_eigen T χ hsep' Finset.univ Φ
      (fun i _ a => hΦT a.1 a.2.1 a.2.2 i) hc
    exact fun i => h i (Finset.mem_univ i)

  intro i
  have hcoef : ∀ m : ℕ, (∑ d ∈ Nat.divisors (M / L i),
      c i d * (if d ∣ m then ModularFormClass.qCoeff (⇑(g i)) (m / d) else 0)) = 0 := by
    intro m
    have h0 := congrArg (fun F : CuspForm (CongruenceSubgroup.Gamma1 M) k => ModularFormClass.qCoeff (⇑F) m) (hΦ0 i)
    rw [qCoeff_zero_form, show Φ i = ∑ d ∈ Nat.divisors (M / L i), c i d • G i d from rfl, qCoeff_sum] at h0
    refine Eq.trans (Finset.sum_congr rfl fun d hd => ?_) h0
    rw [qCoeff_smul, (hGfacts i d (Nat.mem_divisors.mp hd).1).1 m]

  suffices hind : ∀ d₀ : ℕ, d₀ ∈ Nat.divisors (M / L i) → c i d₀ = 0 from hind
  intro d₀
  induction d₀ using Nat.strong_induction_on with
  | _ d₀ ih =>
    intro hd₀
    have hd₀' := Nat.mem_divisors.mp hd₀
    have hd₀pos : 0 < d₀ := Nat.pos_of_mem_divisors hd₀
    have h := hcoef d₀
    rw [Finset.sum_eq_single d₀] at h
    · rwa [if_pos (dvd_refl d₀), Nat.div_self hd₀pos, (hg i).qCoeff_one, mul_one] at h
    · intro d hd hne
      by_cases hdd : d ∣ d₀
      · have hlt : d < d₀ := lt_of_le_of_ne (Nat.le_of_dvd hd₀pos hdd) hne
        rw [ih d hlt hd, zero_mul]
      · rw [if_neg hdd, mul_zero]
    · intro h'; exact absurd hd₀ h'

end CuspForm.M4aIndep

end

open scoped MatrixGroups ModularForm in

theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (n : ℕ) (L : Fin n → ℕ) [∀ i, NeZero (L i)] (hL : ∀ i, L i ∣ M)
    (ε : (i : Fin n) → DirichletCharacter ℂ (L i))
    (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
    (hg : ∀ i, CuspForm.IsEigenformWith (ε i) (g i))
    (hsep : ∀ i j : Fin n, i ≠ j → ∃ p : ℕ, p.Prime ∧ ¬ p ∣ M ∧
      ModularFormClass.qCoeff (g i) p ≠ ModularFormClass.qCoeff (g j) p)
    (G : Fin n → ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hG : ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
      ∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ))
    (c : Fin n → ℕ → ℂ)
    (hc : (∑ i, ∑ d ∈ Nat.divisors (M / L i), c i d • G i d) = 0) :
    ∀ (i : Fin n), ∀ d ∈ Nat.divisors (M / L i), c i d = 0 :=
  CuspForm.M4aIndep.main M k n L hL ε g hg hsep G hG c hc

end S_CuspForm_linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne
end P2MW
export P2MW.S_CuspForm_linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne (solution)
