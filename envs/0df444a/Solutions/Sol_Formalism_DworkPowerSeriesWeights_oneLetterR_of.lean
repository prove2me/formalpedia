-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.oneLetterR_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:04:26.69962+00:00
-- url     : https://prove2.me/submissions/08c8b0f1-a9bc-4225-944f-5c3e298b2822

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_one_le_norm_two
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_lin_wt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_lin_const
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_smul_wt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_smul_const
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_zmod2
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_fintype
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_nonneg
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_pureMon
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_monoWtGe_rad
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (hS : LemmaS.{u}) (hG : GenLogWeight.{u, 0}) (hB : LogBridges.{u})
    (hW1 : SubstWt.{u, 0, v}) (hW0 : SubstWt.{u, 0, 0}) (hRM : RadMono.{u, v})
    (hMW : MulWtLe.{u, v}) (hE : ExpWtLe.{u, v}) (hF : FactVal.{u, v})
    (hOR : OneLetterRadius) : OneLetterR.{u, v} := by
  intro K _ _ _ l N0 N1 hl hodd hpi K0 hK0 ζ hζ be hbe ep hep ι _ _ M hM g hg0 hgl U hU sgn hsgn κ
  classical
  have h2n : 1 ≤ ‖(2 : K)‖ := asmOne_one_le_norm_two hodd hpi
  set π : ℝ := ‖(l : K)‖ with hπdef
  have hl3 : 3 ≤ l := by
    obtain ⟨m, rfl⟩ := hodd
    rcases m with _ | m
    · exact absurd hl Nat.not_prime_one
    · omega
  have hπ0 : 0 < π := by
    rw [hπdef, norm_pos_iff]
    exact_mod_cast hl.ne_zero
  have hπ1 : π ≤ 1 := hpi.le
  have hlR : (3 : ℝ) ≤ l := by exact_mod_cast hl3
  have hl1 : (l : ℝ) - 1 ≠ 0 := by linarith
  have hl2 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hl2p : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
  obtain ⟨hOR1, hOR2⟩ := hOR l hl3
  have hrho0 : 0 ≤ rho l := by
    unfold rho
    positivity
  have hrg : rho l ≤ gam l := by
    unfold rho gam
    gcongr
    linarith
  have key : 1 / ((l : ℝ) - 1) - gam l = rho l := by
    unfold rho gam
    field_simp
    ring

  have wt_sum : ∀ (r : ι → ℝ) (w : ℝ) (s : Finset (Fin N0 × Fin N1))
      (f : Fin N0 × Fin N1 → MvPowerSeries ι K), (∀ x ∈ s, WtGe π r w (f x)) →
      WtGe π r w (∑ x ∈ s, f x) := by
    intro r w s f
    refine Finset.induction_on s ?_ ?_
    · intro _ n
      unfold MonoWtGe
      rw [Finset.sum_empty, map_zero, norm_zero]
      exact Real.rpow_nonneg hπ0.le _
    · intro a s ha ih hf n
      rw [Finset.sum_insert ha]
      have h1 := hf a (Finset.mem_insert_self a s) n
      have h2 := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)) n
      unfold MonoWtGe at h1 h2 ⊢
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

  have cc_subst : ∀ (a : ZMod 2 → MvPowerSeries ι K), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      ∀ f : MvPowerSeries (ZMod 2) K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by
    intro a ha f hf
    have hs : MvPowerSeries.HasSubst a := by
      first
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
        | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
    rw [MvPowerSeries.constantCoeff_subst hs]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hd : d = 0
    · subst hd
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    · obtain ⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by
        by_contra h
        push_neg at h
        exact hd (Finsupp.ext h)
      have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
        rw [Finsupp.prod, map_prod]
        exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs') (by rw [map_pow, ha, zero_pow hs'])
      rw [h0, smul_zero]
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := by
    by_contra h
    have h' := hbe.2.2.1 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
    exact absurd h'.1 (by simp [degE])

  have hUw : WtGe π (fun _ => rho l) 0 U := by
    intro n
    unfold MonoWtGe
    refine (hU n).trans ?_
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hπ0 hπ1
      (by linarith [asmR_dot_nonneg n (r := fun _ => rho l) (fun _ => hrho0)])
  have hlog : ∀ x, oneLog (K := K) l x = genLog (K := K) l id x := fun x => (hB K l 2 N0 N1).2.2 x
  have hgw : ∀ x, WtGe π (fun _ => rho l) (rho l) (g x) :=
    hG K l hl hpi (Fin N0 × Fin N1) id g hg0 (fun x => by rw [← hlog x]; exact hgl x)
  have hGU : WtGe π (fun _ => rho l) 0 (MvPowerSeries.subst g U) :=
    hW0 K π hπ0 hpi (Fin N0 × Fin N1) (Fin N0 × Fin N1) g (fun _ => rho l) (fun _ => rho l) 0 U
      hg0 hgw hUw
  have hlinw : ∀ (t : ℝ) x,
      WtGe π (fun _ : ι => t) t (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) :=
    fun t x => asmOne_lin_wt hπ0 (M x) (hM x) t
  have hlinA : ∀ x, WtGe π (fun _ : ι => gam l) (rho l)
      (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) := fun x =>
    (hRM K π hπ0 hpi ι (fun _ => rho l) (fun _ => gam l) (rho l) (fun _ => hrg)).1 _ (hlinw (rho l) x)
  have hA : WtGe π (fun _ : ι => gam l) 0
      (MvPowerSeries.subst (fun x => ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i)
        (MvPowerSeries.subst g U)) :=
    hW1 K π hπ0 hpi (Fin N0 × Fin N1) ι _ (fun _ => rho l) (fun _ => gam l) 0 _
      (fun x => asmOne_lin_const (M x)) hlinA hGU
  obtain ⟨hS1, hS2⟩ := hS K l 2 hl hodd le_rfl even_two hpi K0 hK0 ζ hζ be hbe
  have hbeW : WtGe π (fun _ : ZMod 2 => gam l) (1 / ((l : ℝ) - 1)) be := by
    intro n
    by_cases hbi : IsBiPower l n
    · obtain ⟨s, s', α, β, hs, hs', _, hsum, rfl⟩ := hbi
      have h1 := hS1 (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))
      unfold MonoWtGe at h1 ⊢
      have hodd' : Odd (α + β) := by
        have h := asmOne_zmod2 s s' α β hs hs' hsum
        have h' : ((α + β : ℕ) : ZMod 2) = 1 := by
          push_cast
          exact h
        have h'' := congrArg ZMod.val h'
        rw [ZMod.val_natCast] at h''
        exact Nat.odd_iff.2 (h''.trans (by decide))
      have hD := hOR1 α β hodd'
      have e1 : dot (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) (fun _ : ZMod 2 => rho l) =
          ((l : ℝ) ^ α + (l : ℝ) ^ β) * rho l := by
        rw [show Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β) = pureMon l s s' α β from rfl,
          asmR_dot_pureMon]
        ring
      have e2 : dot (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) (fun _ : ZMod 2 => gam l) =
          ((l : ℝ) ^ α + (l : ℝ) ^ β) * gam l := by
        rw [show Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β) = pureMon l s s' α β from rfl,
          asmR_dot_pureMon]
        ring
      rw [e1] at h1
      rw [e2]
      refine h1.trans (Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1 ?_)
      have hg : gam l - rho l = 1 / ((l : ℝ) + 1) := by linarith [hOR2]
      have h3 : 1 ≤ ((l : ℝ) ^ α + (l : ℝ) ^ β) * (gam l - rho l) := by
        rw [hg, mul_one_div]
        exact hD
      nlinarith
    · exact asmR_monoWtGe_rad hπ0 hπ1 (fun _ => hrg) (hS2 n hbi)
  have haw : ∀ x (s : ZMod 2), WtGe π (fun _ : ι => gam l) (gam l)
      ((if s = 0 then (1 : K) else ep) • ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) := by
    intro x s
    refine asmOne_smul_wt ?_ (hlinw (gam l) x)
    split_ifs <;> simp [hep]
  have hac : ∀ x (s : ZMod 2), MvPowerSeries.constantCoeff
      ((if s = 0 then (1 : K) else ep) • ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) = 0 :=
    fun x s => asmOne_smul_const _ (asmOne_lin_const (M x))
  have hBx : ∀ x, WtGe π (fun _ : ι => gam l) (1 / ((l : ℝ) - 1))
      (MvPowerSeries.subst (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
        ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be) := fun x =>
    hW1 K π hπ0 hpi (ZMod 2) ι _ (fun _ => gam l) (fun _ => gam l) _ be (hac x) (haw x) hbeW
  have hsgn1 : ‖sgn‖ = 1 := by rcases hsgn with rfl | rfl <;> simp
  have hsgn2 : ‖sgn / 2‖ ≤ 1 := by
    rw [norm_div, hsgn1]
    exact div_le_one_of_le₀ h2n (by positivity)
  have hBw := asmOne_smul_wt hsgn2 (wt_sum _ _ Finset.univ _ (fun x _ => hBx x))
  have hBc : MvPowerSeries.constantCoeff ((sgn / 2) • ∑ x : Fin N0 × Fin N1,
      MvPowerSeries.subst (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
        ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be) = 0 := by
    refine asmOne_smul_const _ ?_
    rw [map_sum]
    exact Finset.sum_eq_zero fun x _ => cc_subst _ (hac x) be hbe0
  have hExp := hE K l hl hpi ι (fun _ => gam l) κ _ hBc (fun n _ => hBw n)
  have hMul := hMW K π hπ0 ι (fun _ => gam l) 0 0 κ _ _ (fun n _ => hA n) hExp
  have hk := hMul κ le_rfl
  have hf := hF K l hl hpi ι κ
  unfold MonoWtGe at hk
  have hdeg : (κ.degree : ℝ) = ∑ i, (κ i : ℝ) := by
    rw [Finsupp.degree_eq_sum]
    push_cast
    rfl
  have e : (∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - ∑ i, (κ i : ℝ) * gam l = rho l * ∑ i, (κ i : ℝ) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← key]
    ring
  rw [norm_mul]
  refine (mul_le_mul hf hk (norm_nonneg _) (Real.rpow_nonneg hπ0.le _)).trans (le_of_eq ?_)
  rw [← Real.rpow_add hπ0, asmR_dot_fintype, hdeg]
  congr 1
  beta_reduce
  linarith [e]
end Formalism.DworkPowerSeriesWeights
