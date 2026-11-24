-- Prove2me | solution 1 for Formalism.GM.badCrit_pairs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:00.727266+00:00
-- url     : https://prove2.me/submissions/c7567eda-cdae-4192-b212-5fa8ab5c3188

import Definitions.Def_Formalism_MahlerMeasure_StatementT
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_BadCrit
import Theorems.Thm_Formalism_GM_badCrit_core
import Theorems.Thm_Formalism_GM_badCrit_be_smul_left
import Theorems.Thm_Formalism_GM_badCrit_be_smul_right
import Theorems.Thm_Formalism_GM_badCrit_torsionFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Module
variable {p : ℕ} [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]
namespace Formalism.GM
theorem _root_.solution (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (L L₁ : Submodule ℤ_[p] Vs) (D : ℤ)
    [Module.Finite ℤ_[p] L] (hle : L₁ ≤ L)
    (hprim : ∀ u ∈ L₁, (∀ (a : ℤ_[p]) (x : Vs), x ∈ L₁ → u = a • x → IsUnit a) →
      ∃ u' ∈ L, (p : ℝ) ^ (-D) ≤ ‖be u u'‖) :
    ∃ x y : Fin (Module.finrank ℤ_[p] L₁) → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0 := by
  classical
  have := badCrit_torsionFree (p := p) (Vs := Vs)
  have : Module.Finite ℤ_[p] L₁ :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  set m := Module.finrank ℤ_[p] L₁
  let u := Module.finBasis ℤ_[p] L₁
  let bL := Module.finBasis ℤ_[p] L
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpq : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set C : ℝ := ∑ a, ∑ b, ‖be (u a) (bL b)‖
  have hC : ∀ w ∈ L, ∀ a, ‖be (u a) w‖ ≤ C := by
    intro w hw a
    have hw' : w = ∑ b, (bL.repr ⟨w, hw⟩ b) • (bL b : Vs) := by
      have := congrArg Subtype.val (bL.sum_repr ⟨w, hw⟩)
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    rw [hw', map_sum]
    calc ‖∑ b, be (u a) ((bL.repr ⟨w, hw⟩ b) • (bL b : Vs))‖
        ≤ ∑ b, ‖be (u a) ((bL.repr ⟨w, hw⟩ b) • (bL b : Vs))‖ := norm_sum_le _ _
      _ ≤ ∑ b, ‖be (u a) (bL b)‖ := by
          gcongr with b
          rw [badCrit_be_smul_right, norm_mul, ← PadicInt.norm_def]
          exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)
      _ ≤ C := Finset.single_le_sum (f := fun a => ∑ b, ‖be (u a) (bL b)‖)
          (fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _) (Finset.mem_univ a)
  obtain ⟨E, hE⟩ := pow_unbounded_of_one_lt (C * (p : ℝ) ^ D) hp1
  have hCE : C ≤ (p : ℝ) ^ ((E : ℤ) - D) := by
    rw [zpow_sub₀ hp0.ne', zpow_natCast, le_div_iff₀ (zpow_pos hp0 _)]
    exact hE.le
  have hnp : ∀ z : ℤ, ‖(p : ℚ_[p]) ^ z‖ = (p : ℝ) ^ (-z) := by
    intro z
    exact Padic.norm_p_zpow z
  have hint : ∀ w ∈ L, ∀ a, ‖(p : ℚ_[p]) ^ ((E : ℤ) - D) * be (u a) w‖ ≤ 1 := by
    intro w hw a
    rw [norm_mul, hnp]
    calc (p : ℝ) ^ (-((E : ℤ) - D)) * ‖be (u a) w‖
        ≤ (p : ℝ) ^ (-((E : ℤ) - D)) * (p : ℝ) ^ ((E : ℤ) - D) := by
          gcongr; exact (hC w hw a).trans hCE
      _ = 1 := by rw [← zpow_add₀ hp0.ne']; simp
  let g : L → Fin m → ℤ_[p] := fun w a => ⟨(p : ℚ_[p]) ^ ((E : ℤ) - D) * be (u a) w, hint w.1 w.2 a⟩
  have hg : ∀ w a, ((g w a : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ ((E : ℤ) - D) * be (u a) w :=
    fun _ _ => rfl
  let G : L →ₗ[ℤ_[p]] (Fin m → ℤ_[p]) :=
    { toFun := g
      map_add' := fun w w' => by
        funext a; apply PadicInt.ext
        rw [Pi.add_apply, PadicInt.coe_add, hg, hg, hg, Submodule.coe_add, map_add, mul_add]
      map_smul' := fun c w => by
        funext a; apply PadicInt.ext
        rw [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, PadicInt.coe_mul, hg, hg,
          Submodule.coe_smul, badCrit_be_smul_right]
        ring }
  have hG : ∀ w a, ((G w a : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ ((E : ℤ) - D) * be (u a) w :=
    fun _ _ => rfl
  have hcore := badCrit_core E (LinearMap.range G) (by
    rintro l ⟨z0, hz0⟩
    set c : Fin m → ℤ_[p] := fun a => l (fun j => if a = j then 1 else 0)
    have hl : ∀ z, l z = ∑ a, z a * c a := fun z => by
      rw [LinearMap.pi_apply_eq_sum_univ l z]; rfl
    set uu : L₁ := u.equivFun.symm c
    have huu : (uu : Vs) = ∑ a, c a • (u a : Vs) := by
      show ((u.equivFun.symm c : L₁) : Vs) = _
      rw [Basis.equivFun_symm_apply, Submodule.coe_sum]
      rfl
    have hprim' : ∀ (b : ℤ_[p]) (x : Vs), x ∈ L₁ → (uu : Vs) = b • x → IsUnit b := by
      intro b x hx hbx
      have h1 : uu = b • (⟨x, hx⟩ : L₁) := Subtype.ext hbx
      have h2 : c = b • u.equivFun ⟨x, hx⟩ := by
        rw [← u.equivFun.apply_symm_apply c]
        change u.equivFun uu = _
        rw [h1, map_smul]
      apply IsUnit.of_mul_eq_one (∑ a, z0 a * u.equivFun ⟨x, hx⟩ a)
      rw [← hz0, hl, h2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    obtain ⟨u', hu', hn⟩ := hprim uu uu.2 hprim'
    refine ⟨G ⟨u', hu'⟩, LinearMap.mem_range_self _ _, ?_⟩
    have hq : ((l (G ⟨u', hu'⟩) : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ ((E : ℤ) - D) * be uu u' := by
      rw [hl, PadicInt.coe_sum, huu, map_sum, LinearMap.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [PadicInt.coe_mul, hG, badCrit_be_smul_left]; ring
    rw [PadicInt.norm_def, hq, norm_mul, hnp]
    calc (p : ℝ) ^ (-(E : ℤ)) = (p : ℝ) ^ (-((E : ℤ) - D)) * (p : ℝ) ^ (-D) := by
          rw [← zpow_add₀ hp0.ne']; ring_nf
      _ ≤ _ := by gcongr)
  have hw : ∀ j : Fin m, ∃ w : L, G w = (p : ℤ_[p]) ^ E • Pi.single j 1 :=
    fun j => LinearMap.mem_range.1 (hcore (Pi.single j 1))
  choose w hw using hw
  refine ⟨fun i => (u i : Vs), fun j => (w j : Vs), fun i => hle (u i).2, fun j => (w j).2, ?_⟩
  intro i j
  have h1 := congrArg (fun z => ((z i : ℤ_[p]) : ℚ_[p])) (hw j)
  simp only [hG] at h1
  have h2 : ((((p : ℤ_[p]) ^ E • (Pi.single j 1 : Fin m → ℤ_[p])) i : ℤ_[p]) : ℚ_[p]) =
      (p : ℚ_[p]) ^ ((E : ℤ) - D) * (if i = j then (p : ℚ_[p]) ^ D else 0) := by
    rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one, ← zpow_add₀ hpq]; push_cast; simp
    · simp
  rw [h2] at h1
  exact mul_left_cancel₀ (zpow_ne_zero _ hpq) h1
end Formalism.GM
