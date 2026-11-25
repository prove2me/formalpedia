-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.sumV_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:33.829321+00:00
-- url     : https://prove2.me/submissions/4d20850e-d5e5-4cf1-8b71-14cc70e922a5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_alongCv_congr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_congr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_tyS
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_curve_eq_ex_lg
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_RawChart_Vpow_mem__c20d29e22a82
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_sum_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_subst_zero


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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
namespace Formalism.L2.FormalSeriesBounds.RawChart
theorem _root_.solution (V : VF C) (g : Fin 2) (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hex0 : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (hlgex : ∀ i, MvPowerSeries.subst X.ex (X.lg i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g)
    (hadd : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g)
    (y : ℕ → ℕ → I g ⊕ JJ I g → C) (hy : ∀ s, y s ∈ X.TySet V g) : sumV y ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  have hP : ∀ N : ℕ, ∑ s ∈ Finset.range N, Vpow s (y s) ∈ X.TySet V g := fun N =>
    X.sum_mem V g h0 hadd _ _ fun s _ => X.Vpow_mem' V g s _ (hy s)
  have hPeq : ∀ N i, i < N → ∀ n, (∑ s ∈ Finset.range N, Vpow s (y s)) i n = sumV y i n := by
    intro N i hi n
    rw [Finset.sum_apply, Finset.sum_apply]
    show ∑ s ∈ Finset.range N, (if i < s then 0 else y s (i - s) n) = ∑ s ∈ Finset.range (i + 1), y s (i - s) n
    have hsub : Finset.range (i + 1) ⊆ Finset.range N := Finset.range_subset_range.2 (by omega)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun s hs => ?_
      rw [if_neg]
      have := Finset.mem_range.1 hs
      omega
    · intro s _ hs
      rw [if_pos]
      have : ¬ s < i + 1 := fun h => hs (Finset.mem_range.2 h)
      omega
  choose γN lamN hγN hlamN h1N h2N using hP
  set A : κ → PowerSeries C := fun i => ∑ c : I g, X.u g c i • tyS V.l (fun s => sumV y s (Sum.inl c)) with hA
  have hA0 : ∀ i, PowerSeries.constantCoeff (A i) = 0 := by
    intro i
    rw [hA]
    show PowerSeries.constantCoeff (∑ c : I g, X.u g c i • tyS V.l (fun s => sumV y s (Sum.inl c))) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_tyS hl2, smul_zero]
  set γ : κ → PowerSeries C := fun i => alongCv A (X.ex i) with hγdef
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => constantCoeff_subst_zero hA0 (hex0 i)
  have hlgγ : ∀ i, alongCv γ (X.lg i) = A i := by
    intro i
    have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero hA0
    have e1 : MvPowerSeries.subst A (MvPowerSeries.subst X.ex (X.lg i)) = A i := by
      rw [hlgex i, MvPowerSeries.subst_X hS]
    rw [← e1, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hex0) hS]
    rfl
  have htyN : ∀ N n, ∀ m < V.l ^ N, PowerSeries.coeff m (tyS V.l fun s => sumV y s n) =
      PowerSeries.coeff m (tyS V.l fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s n) := by
    intro N n m hm
    exact coeff_tyS_congr hl2 _ _ N (fun i hi => (hPeq N i hi n).symm) m hm
  have hγN' : ∀ N i, ∀ m < V.l ^ N, PowerSeries.coeff m (γ i) = PowerSeries.coeff m (γN N i) := by
    intro N i m hm
    rw [X.curve_eq_ex_lg hlg0 hexlg (γN N) (fun i => (hγN N i).1) i]
    refine coeff_alongCv_congr hA0 (fun j => constantCoeff_subst_zero (fun i => (hγN N i).1) (hlg0 j)) ?_ _ m hm
    intro j m' hm'
    show PowerSeries.coeff m' (∑ c : I g, X.u g c j • tyS V.l (fun s => sumV y s (Sum.inl c))) =
      PowerSeries.coeff m' (alongCv (γN N) (X.lg j))
    rw [h1N N j]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul, htyN N _ m' hm']
  have hγI : IsCv V γ := by
    intro i
    refine ⟨hγ0 i, fun n => ?_⟩
    rw [hγN' n i n (Nat.lt_pow_self (by omega))]
    exact (hγN n i).2 n
  set lam : JJ I g → PowerSeries C := fun q => tyS V.l (fun s => sumV y s (Sum.inr q)) +
      alongCv γ (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => sumV y s (Sum.inl c)) else 0) with hlamdef
  have hlamN' : ∀ N q, ∀ m < V.l ^ N, PowerSeries.coeff m (lam q) = PowerSeries.coeff m (lamN N q) := by
    intro N q m hm
    have e : lamN N q = tyS V.l (fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s (Sum.inr q)) +
        alongCv (γN N) (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) •
          tyS V.l (fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s (Sum.inl c)) else 0) := by
      rw [h2N N q]
      abel
    rw [e, hlamdef]
    show PowerSeries.coeff m (tyS V.l (fun s => sumV y s (Sum.inr q)) +
      alongCv γ (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => sumV y s (Sum.inl c)) else 0)) = _
    rw [map_sub, map_sub, map_add, map_add, map_sum, map_sum, htyN N _ m hm,
      coeff_alongCv_congr hγ0 (fun i => (hγN N i).1) (fun i => hγN' N i) _ m hm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul, htyN N _ m hm]
    · rfl
  have hlamI : IsCv V lam := by
    intro q
    refine ⟨?_, fun n => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hlamN' 0 q 0 (by simp),
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (hlamN 0 q).1
    · rw [hlamN' n q n (Nat.lt_pow_self (by omega))]
      exact (hlamN n q).2 n
  refine ⟨γ, lam, hγI, hlamI, hlgγ, ?_⟩
  intro q
  have hab : ∀ a b c : PowerSeries C, a = (a + b - c) - b + c := by
    intro a b c
    abel
  exact hab _ _ _
end Formalism.L2.FormalSeriesBounds.RawChart
