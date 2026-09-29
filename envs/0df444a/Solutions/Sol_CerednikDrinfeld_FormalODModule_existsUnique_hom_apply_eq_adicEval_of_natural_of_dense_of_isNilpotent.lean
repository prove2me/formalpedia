-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.existsUnique_hom_apply_eq_adicEval_of_natural_of_dense_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/4f746241-742a-5612-b579-dc9098f1b121

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_CerednikDrinfeld_FormalODModule_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_hom_apply_eq_adicEval_of_natural_of_dense_of_isNilpotent

set_option autoImplicit false

open MvPowerSeries

universe u v w z

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 SpecialFormal.Series SpecialFormal.Series.id SpecialFormal.Series.addVia SpecialFormal.Series.constantCoeff_comp FormalODModule FormalODModule.existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent"
namespace FormalODModule
p2m_export "CerednikDrinfeld.FormalODModule" "act_natCast Hom F varpi act_mul isLawHom_act act_add act_one act isLawHom_varpi existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent"
namespace NilDenseEquiv
p2m_open "CerednikDrinfeld.FormalODModule CerednikDrinfeld"

section Engine

variable {R : Type u} [CommRing R] {C : Type v} [CommRing C] [Algebra R C] {σ : Type w}

theorem isAdicComplete_of_isNilpotent (J : Ideal C) (hJ : IsNilpotent J) : IsAdicComplete J C := by
  obtain ⟨n, hn⟩ := hJ
  haveI : IsHausdorff J C := ⟨fun x hx => by
    have := hx n
    rw [hn] at this
    simpa [SModEq.zero] using this⟩
  haveI : IsPrecomplete J C := ⟨fun {f} hf => ⟨f n, fun m => by
    by_cases hm : m ≤ n
    · exact hf hm
    · push Not at hm
      have h1 : f n ≡ f m [SMOD (J ^ n • ⊤ : Submodule C C)] := hf hm.le
      have h2 : (J ^ m • ⊤ : Submodule C C) = ⊥ := by
        rw [show m = n + (m - n) by omega, pow_add, hn, zero_mul]; simp
      have h3 : (J ^ n • ⊤ : Submodule C C) = ⊥ := by rw [hn]; simp
      rw [h2]; rw [h3] at h1
      exact h1.symm⟩⟩
  exact ⟨⟩

theorem prod_pow_eq_zero_of_le_degree (J : Ideal C) {N : ℕ} (hN : J ^ N = ⊥) {x : σ → C}
    (hx : ∀ s, x s ∈ J) (d : σ →₀ ℕ) (hd : N ≤ d.degree) :
    (d.prod fun s e => x s ^ e) = 0 := by
  have hmem : (d.prod fun s e => x s ^ e) ∈ J ^ d.degree := by
    rw [Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun s _ => Ideal.pow_mem_pow (hx s) _
  have hle : J ^ d.degree ≤ J ^ N := Ideal.pow_le_pow_right hd
  have := hle hmem
  rwa [hN, Submodule.mem_bot] at this

theorem adicEval_eq_sum [Finite σ] (J : Ideal C) {N : ℕ} (hN : J ^ N = ⊥) {x : σ → C}
    (hx : ∀ s, x s ∈ J) (f : MvPowerSeries σ R) (D : Finset (σ →₀ ℕ))
    (hD : ∀ d, d ∉ D → N ≤ d.degree) :
    MvFormalGroup.adicEval J x f = ∑ d ∈ D, algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal C := ⟨J⟩
  haveI hc : IsAdicComplete J C := isAdicComplete_of_isNilpotent J ⟨N, hN⟩
  haveI : CompleteSpace C := ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp hc).1
  haveI : T2Space C := ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp hc).2
  have hφ : Continuous (algebraMap R C) := continuous_of_discreteTopology
  have ha : MvPowerSeries.HasEval x := by
    refine ⟨fun s => ?_, ?_⟩
    · apply tendsto_atTop_of_eventually_const (i₀ := N)
      intro n hn
      have h0 : x s ^ n = 0 := by
        have hmem : x s ^ n ∈ J ^ n := Ideal.pow_mem_pow (hx s) n
        have := (Ideal.pow_le_pow_right hn) hmem
        rwa [hN, Submodule.mem_bot] at this
      exact h0
    · rw [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
  have h1 := MvPowerSeries.hasSum_eval₂ hφ ha f
  have h2 : HasSum (fun d : σ →₀ ℕ => algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e)
      (∑ d ∈ D, algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e) := by
    apply hasSum_sum_of_ne_finset_zero
    intro d hd'
    rw [prod_pow_eq_zero_of_le_degree J hN hx d (hD d hd'), mul_zero]
  exact h1.unique h2

theorem le_degree_of_not_mem_Iic [Fintype σ] [DecidableEq σ] (N : ℕ) (d : σ →₀ ℕ)
    (hd : d ∉ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : σ => N)) : N ≤ d.degree := by
  classical
  rw [Finset.mem_Iic] at hd
  have : ∃ s, N < d s := by
    by_contra h
    push Not at h
    exact hd fun s => by simpa using h s
  obtain ⟨s, hs⟩ := this
  calc N ≤ d s := hs.le
    _ ≤ d.degree := by
        rw [Finsupp.degree_apply]
        by_cases hs0 : s ∈ d.support
        · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hs0
        · rw [Finsupp.notMem_support_iff.mp hs0]; exact Nat.zero_le _

theorem adicEval_mem [Finite σ] (J : Ideal C) (hJ : IsNilpotent J) {x : σ → C} (hx : ∀ s, x s ∈ J)
    {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) : MvFormalGroup.adicEval J x f ∈ J := by
  classical
  haveI := Fintype.ofFinite σ
  obtain ⟨N, hN⟩ := hJ
  replace hN : J ^ N = ⊥ := hN
  rw [adicEval_eq_sum J hN hx f _ (le_degree_of_not_mem_Iic N)]
  refine Ideal.sum_mem _ fun d _ => ?_
  by_cases hd : d = 0
  · subst hd
    simp [hf]
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push Not at h
      exact hd (Finsupp.ext fun s => by simpa using h s)
    refine Ideal.mul_mem_left _ _ ?_
    rw [Finsupp.prod]
    have hs' : s ∈ d.support := Finsupp.mem_support_iff.mpr hs
    rw [← Finset.mul_prod_erase _ _ hs']
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs
    rw [hk, pow_succ]
    exact Ideal.mul_mem_left _ _ (hx s)

end Engine

section Points

variable {p : ℕ} [Fact p.Prime] {L : Type u} [CommRing L]

theorem adicEval_subst_of_isNilpotent {C : Type u} [CommRing C] [Algebra L C] (J : Ideal C)
    (hJ : IsNilpotent J) {x : Fin 2 → C} (hx : ∀ j, x j ∈ J) {φ : SpecialFormal.Series L}
    (hφ : ∀ i, (φ i).constantCoeff = 0) (g : MvPowerSeries (Fin 2) L) :
    MvFormalGroup.adicEval J x (subst φ g) =
      MvFormalGroup.adicEval J (fun j => MvFormalGroup.adicEval J x (φ j)) g := by
  haveI := isAdicComplete_of_isNilpotent J hJ
  exact MvFormalGroup.adicEval_subst J (fun j => Ideal.le_radical (hx j))
    (hasSubst_of_constantCoeff_zero hφ) g

theorem adicEval_comp {C : Type u} [CommRing C] [Algebra L C] (J : Ideal C)
    (hJ : IsNilpotent J) {x : Fin 2 → C} (hx : ∀ j, x j ∈ J) {ψ φ : SpecialFormal.Series L}
    (hφ : ∀ i, (φ i).constantCoeff = 0) (i : Fin 2) :
    MvFormalGroup.adicEval J x ((ψ.comp φ) i) =
      MvFormalGroup.adicEval J (fun j => MvFormalGroup.adicEval J x (φ j)) (ψ i) :=
  adicEval_subst_of_isNilpotent J hJ hx hφ (ψ i)

theorem adicEval_addVia (F : MvFormalGroup 2 L) {C : Type u} [CommRing C] [Algebra L C] (J : Ideal C)
    (hJ : IsNilpotent J) {x : Fin 2 → C} (hx : ∀ j, x j ∈ J) {φ ψ : SpecialFormal.Series L}
    (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0) (i : Fin 2) :
    MvFormalGroup.adicEval J x (SpecialFormal.Series.addVia F φ ψ i) =
      MvFormalGroup.adicEval J
        (Sum.elim (fun j => MvFormalGroup.adicEval J x (φ j)) fun j => MvFormalGroup.adicEval J x (ψ j))
        (F.toPowerSeries i) := by
  haveI := isAdicComplete_of_isNilpotent J hJ
  exact MvFormalGroup.adicEval_subst_elim F J (fun j => Ideal.le_radical (hx j)) hφ hψ i

theorem adicEval_elim_zero_right (F : MvFormalGroup 2 L) {C : Type u} [CommRing C] [Algebra L C]
    (J : Ideal C) (hJ : IsNilpotent J) {y : Fin 2 → C} (hy : ∀ j, y j ∈ J) (i : Fin 2) :
    MvFormalGroup.adicEval J (Sum.elim y fun _ => (0 : C)) (F.toPowerSeries i) = y i := by
  haveI := isAdicComplete_of_isNilpotent J hJ
  let P : F.Points C J := ⟨y, fun j => Ideal.le_radical (hy j)⟩
  have h := congrArg MvFormalGroup.Points.val (add_zero P)
  exact congrFun h i

theorem adicEval_elim_zero_left (F : MvFormalGroup 2 L) {C : Type u} [CommRing C] [Algebra L C]
    (J : Ideal C) (hJ : IsNilpotent J) {y : Fin 2 → C} (hy : ∀ j, y j ∈ J) (i : Fin 2) :
    MvFormalGroup.adicEval J (Sum.elim (fun _ => (0 : C)) y) (F.toPowerSeries i) = y i := by
  haveI := isAdicComplete_of_isNilpotent J hJ
  let P : F.Points C J := ⟨y, fun j => Ideal.le_radical (hy j)⟩
  have h := congrArg MvFormalGroup.Points.val (zero_add P)
  exact congrFun h i

theorem adicEval_id {C : Type u} [CommRing C] [Algebra L C] (J : Ideal C) (x : Fin 2 → C) (i : Fin 2) :
    MvFormalGroup.adicEval J x (SpecialFormal.Series.id L i) = x i :=
  MvFormalGroup.adicEval_X J x i

end Points

section Torsion

variable {p : ℕ} [Fact p.Prime] {L : Type u} [CommRing L]

theorem exists_eq_single_of_degree_eq_one {σ : Type*} (d : σ →₀ ℕ) (hd : d.degree = 1) :
    ∃ j, d = Finsupp.single j 1 := by
  have hmem : d ∈ {d : σ →₀ ℕ | d.degree = 1} := hd
  rw [← Finsupp.range_single_one] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact ⟨j, hj.symm⟩

theorem coeff_single_nthSeries (F : MvFormalGroup 2 L) (n : ℕ) (i j : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single j 1) (F.nthSeries n i) = if i = j then (n : L) else 0 := by
  have h := MvFormalGroup.linearPart_nthSeries F n
  have hij := congrFun (congrFun h i) j
  change MvPowerSeries.coeff (Finsupp.single j 1) (F.nthSeries n i) =
    (n • (1 : Matrix (Fin 2) (Fin 2) L)) i j at hij
  rw [hij, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem adicEval_act_p_mem_pow (X : FormalODModule p L) {C : Type u} [CommRing C] [Algebra L C]
    (J : Ideal C) (hJ : IsNilpotent J) (P : Ideal C) (hpP : (p : C) ∈ P)
    {e : ℕ} (he : 1 ≤ e) {z : Fin 2 → C} (hz : ∀ j, z j ∈ J) (hzP : ∀ j, z j ∈ P ^ e) (i : Fin 2) :
    MvFormalGroup.adicEval J z (X.act (p : Zp2 p) i) ∈ P ^ (e + 1) := by
  classical
  obtain ⟨N, hN⟩ := hJ
  replace hN : J ^ N = ⊥ := hN
  rw [X.act_natCast, adicEval_eq_sum J hN hz _ _ (le_degree_of_not_mem_Iic N)]
  refine Ideal.sum_mem _ fun d _ => ?_
  rcases Nat.lt_or_ge d.degree 2 with hlt | hge
  · rcases Nat.lt_or_ge d.degree 1 with h0 | h1
    ·
      have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
      subst hd0
      have hc : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) (X.F.nthSeries p i) = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact MvFormalGroup.constantCoeff_nthSeries X.F p i
      rw [hc, map_zero, zero_mul]
      exact Submodule.zero_mem _
    ·
      have hd1 : d.degree = 1 := by omega
      obtain ⟨j, rfl⟩ := exists_eq_single_of_degree_eq_one d hd1
      rw [coeff_single_nthSeries]
      split_ifs with hij
      · rw [map_natCast, Finsupp.prod_single_index (by simp), pow_one, pow_succ']
        exact Ideal.mul_mem_mul hpP (hzP j)
      · rw [map_zero, zero_mul]
        exact Submodule.zero_mem _
  ·
    refine Ideal.mul_mem_left _ _ ?_
    have hmem : (d.prod fun s k => z s ^ k) ∈ P ^ (e * d.degree) := by
      rw [Finsupp.prod, Finsupp.degree_apply, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
      refine Ideal.prod_mem_prod fun s _ => ?_
      rw [pow_mul]
      exact Ideal.pow_mem_pow (hzP s) _
    have hle : e + 1 ≤ e * d.degree := by nlinarith
    exact Ideal.pow_le_pow_right hle hmem

theorem adicEval_act_pow_mem_pow (X : FormalODModule p L) {C : Type u} [CommRing C] [Algebra L C]
    (J : Ideal C) (hJ : IsNilpotent J) (P : Ideal C) (hpP : (p : C) ∈ P) :
    ∀ (n : ℕ) (z : Fin 2 → C), (∀ j, z j ∈ J) → ∀ (e : ℕ), 1 ≤ e → (∀ j, z j ∈ P ^ e) →
      ∀ i, MvFormalGroup.adicEval J z (X.act ((p : Zp2 p) ^ n) i) ∈ P ^ (e + n)
  | 0 => by
    intro z hz e he hzP i
    rw [pow_zero, X.act_one, add_zero]
    show MvFormalGroup.adicEval J z (MvPowerSeries.X i) ∈ P ^ e
    rw [MvFormalGroup.adicEval_X]
    exact hzP i
  | n + 1 => by
    intro z hz e he hzP i
    rw [pow_succ, X.act_mul]
    show MvFormalGroup.adicEval J z (subst (X.act (p : Zp2 p)) (X.act ((p : Zp2 p) ^ n) i)) ∈ _
    rw [adicEval_subst_of_isNilpotent J hJ hz (X.isLawHom_act _).1]
    have hw : ∀ j, MvFormalGroup.adicEval J z (X.act (p : Zp2 p) j) ∈ J :=
      fun j => adicEval_mem J hJ hz ((X.isLawHom_act _).1 j)
    have hwP : ∀ j, MvFormalGroup.adicEval J z (X.act (p : Zp2 p) j) ∈ P ^ (e + 1) :=
      fun j => adicEval_act_p_mem_pow X J hJ P hpP he hz hzP j
    have key := adicEval_act_pow_mem_pow X J hJ P hpP n _ hw (e + 1) (by omega) hwP i
    rwa [show e + 1 + n = e + (n + 1) by omega] at key

theorem exists_forall_adicEval_act_pow_eq_zero (hp : IsNilpotent (p : L))
    {C : Type u} [CommRing C] [Algebra L C] (J : Ideal C) (hJ : IsNilpotent J) :
    ∃ K : ℕ, ∀ (X : FormalODModule p L) (z : Fin 2 → C), (∀ j, z j ∈ J) →
      ∀ i, MvFormalGroup.adicEval J z (X.act ((p : Zp2 p) ^ K) i) = 0 := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := id hJ
  replace hb : J ^ b = ⊥ := hb
  let P : Ideal C := Ideal.span {(p : C)} ⊔ J
  have hpC : (p : C) ^ a = 0 := by
    have := congrArg (algebraMap L C) ha
    rwa [map_pow, map_natCast, map_zero] at this
  have hPpow : P ^ (a + b) = ⊥ := by
    apply le_bot_iff.mp
    calc P ^ (a + b) ≤ Ideal.span {(p : C)} ^ a ⊔ J ^ b := Ideal.sup_pow_add_le_pow_sup_pow
      _ = ⊥ := by
          rw [Ideal.span_singleton_pow, hpC, Ideal.span_singleton_eq_bot.mpr rfl, hb, bot_sup_eq]
  have hpP : (p : C) ∈ P := Ideal.mem_sup_left (Ideal.subset_span rfl)
  refine ⟨a + b, fun X z hz i => ?_⟩
  have hzP : ∀ j, z j ∈ P ^ 1 := fun j => by
    rw [pow_one]
    exact Ideal.mem_sup_right (hz j)
  have hmem := adicEval_act_pow_mem_pow X J hJ P hpP (a + b) z hz 1 le_rfl hzP i
  have hle : P ^ (1 + (a + b)) ≤ P ^ (a + b) := Ideal.pow_le_pow_right (by omega)
  have := hle hmem
  rwa [hPpow, Submodule.mem_bot] at this

end Torsion

section Approx

variable {p : ℕ} [Fact p.Prime] {L : Type u} [CommRing L]

theorem adicEval_act_pow_mul_eq_zero (X : FormalODModule p L) {C : Type u} [CommRing C] [Algebra L C]
    (J : Ideal C) (hJ : IsNilpotent J) {K : ℕ}
    (hK : ∀ z : Fin 2 → C, (∀ j, z j ∈ J) → ∀ i, MvFormalGroup.adicEval J z (X.act ((p : Zp2 p) ^ K) i) = 0)
    (γ : Zp2 p) {x : Fin 2 → C} (hx : ∀ j, x j ∈ J) (i : Fin 2) :
    MvFormalGroup.adicEval J x (X.act ((p : Zp2 p) ^ K * γ) i) = 0 := by
  rw [X.act_mul]
  show MvFormalGroup.adicEval J x (subst (X.act γ) (X.act ((p : Zp2 p) ^ K) i)) = 0
  rw [adicEval_subst_of_isNilpotent J hJ hx (X.isLawHom_act γ).1]
  exact hK _ (fun j => adicEval_mem J hJ hx ((X.isLawHom_act γ).1 j)) i

theorem adicEval_addVia_eq_act (X : FormalODModule p L) {C : Type u} [CommRing C] [Algebra L C]
    (J : Ideal C) (hJ : IsNilpotent J) {K : ℕ}
    (hK : ∀ z : Fin 2 → C, (∀ j, z j ∈ J) → ∀ i, MvFormalGroup.adicEval J z (X.act ((p : Zp2 p) ^ K) i) = 0)
    (a α' β' γ δ : Zp2 p) (hα : α' = a + (p : Zp2 p) ^ K * γ) (hβ : β' = (p : Zp2 p) ^ K * δ)
    {x : Fin 2 → C} (hx : ∀ j, x j ∈ J) :
    (fun i => MvFormalGroup.adicEval J x
        (SpecialFormal.Series.addVia X.F (X.act α') ((X.act β').comp X.varpi) i)) =
      fun i => MvFormalGroup.adicEval J x (X.act a i) := by
  have hψ : ∀ i, (((X.act β').comp X.varpi) i).constantCoeff = 0 :=
    SpecialFormal.Series.constantCoeff_comp (X.isLawHom_act β').1 X.isLawHom_varpi.1
  have hax : ∀ j, MvFormalGroup.adicEval J x (X.act a j) ∈ J :=
    fun j => adicEval_mem J hJ hx ((X.isLawHom_act a).1 j)
  have hvx : ∀ j, MvFormalGroup.adicEval J x (X.varpi j) ∈ J :=
    fun j => adicEval_mem J hJ hx (X.isLawHom_varpi.1 j)

  have h1 : (fun j => MvFormalGroup.adicEval J x (X.act α' j)) = fun j => MvFormalGroup.adicEval J x (X.act a j) := by
    funext j
    rw [hα, X.act_add, adicEval_addVia X.F J hJ hx (X.isLawHom_act a).1 (X.isLawHom_act _).1 j]
    have hz : (fun l => MvFormalGroup.adicEval J x (X.act ((p : Zp2 p) ^ K * γ) l)) = fun _ => (0 : C) :=
      funext fun l => adicEval_act_pow_mul_eq_zero X J hJ hK γ hx l
    rw [hz]
    exact adicEval_elim_zero_right X.F J hJ hax j

  have h2 : (fun j => MvFormalGroup.adicEval J x (((X.act β').comp X.varpi) j)) = fun _ => (0 : C) := by
    funext j
    rw [adicEval_comp J hJ hx X.isLawHom_varpi.1 j, hβ]
    exact adicEval_act_pow_mul_eq_zero X J hJ hK δ hvx j
  funext i
  rw [adicEval_addVia X.F J hJ hx (X.isLawHom_act α').1 hψ i, h1, h2]
  exact adicEval_elim_zero_right X.F J hJ hax i

theorem adicEval_addVia_eq_varpi (X : FormalODModule p L) {C : Type u} [CommRing C] [Algebra L C]
    (J : Ideal C) (hJ : IsNilpotent J) {K : ℕ}
    (hK : ∀ z : Fin 2 → C, (∀ j, z j ∈ J) → ∀ i, MvFormalGroup.adicEval J z (X.act ((p : Zp2 p) ^ K) i) = 0)
    (α' β' γ δ : Zp2 p) (hα : α' = (p : Zp2 p) ^ K * γ) (hβ : β' = 1 + (p : Zp2 p) ^ K * δ)
    {x : Fin 2 → C} (hx : ∀ j, x j ∈ J) :
    (fun i => MvFormalGroup.adicEval J x
        (SpecialFormal.Series.addVia X.F (X.act α') ((X.act β').comp X.varpi) i)) =
      fun i => MvFormalGroup.adicEval J x (X.varpi i) := by
  have hψ : ∀ i, (((X.act β').comp X.varpi) i).constantCoeff = 0 :=
    SpecialFormal.Series.constantCoeff_comp (X.isLawHom_act β').1 X.isLawHom_varpi.1
  have hvx : ∀ j, MvFormalGroup.adicEval J x (X.varpi j) ∈ J :=
    fun j => adicEval_mem J hJ hx (X.isLawHom_varpi.1 j)

  have h1 : (fun j => MvFormalGroup.adicEval J x (X.act α' j)) = fun _ => (0 : C) := by
    funext j
    rw [hα]
    exact adicEval_act_pow_mul_eq_zero X J hJ hK γ hx j

  have h2 : (fun j => MvFormalGroup.adicEval J x (((X.act β').comp X.varpi) j)) =
      fun j => MvFormalGroup.adicEval J x (X.varpi j) := by
    funext j
    rw [adicEval_comp J hJ hx X.isLawHom_varpi.1 j, hβ, X.act_add,
      adicEval_addVia X.F J hJ hvx (X.isLawHom_act 1).1 (X.isLawHom_act _).1 j]
    have hz : (fun l => MvFormalGroup.adicEval J (fun j => MvFormalGroup.adicEval J x (X.varpi j))
        (X.act ((p : Zp2 p) ^ K * δ) l)) = fun _ => (0 : C) :=
      funext fun l => adicEval_act_pow_mul_eq_zero X J hJ hK δ hvx l
    have hid : (fun l => MvFormalGroup.adicEval J (fun j => MvFormalGroup.adicEval J x (X.varpi j))
        (X.act 1 l)) = fun j => MvFormalGroup.adicEval J x (X.varpi j) := by
      funext l
      rw [X.act_one]
      exact adicEval_id J _ l
    rw [hz, hid]
    exact adicEval_elim_zero_right X.F J hJ hvx j
  funext i
  rw [adicEval_addVia X.F J hJ hx (X.isLawHom_act α').1 hψ i, h1, h2]
  exact adicEval_elim_zero_left X.F J hJ hvx i

end Approx

section Main

variable {p : ℕ} [Fact p.Prime] {L : Type u} [CommRing L]

theorem exists_eq_add_pow_mul {k : ℕ} {u v : Zp2 p} (h : u - v ∈ Ideal.span {((p : Zp2 p)) ^ k}) :
    ∃ γ : Zp2 p, u = v + (p : Zp2 p) ^ k * γ := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  exact ⟨c, by rw [mul_comm, hc]; ring⟩

theorem existsUnique_odHom_of_dense (hp : IsNilpotent (p : L))
    (X X' : FormalODModule p L)
    (D : Set (Zp2 p × Zp2 p))
    (hD : ∀ (k : ℕ) (α β : Zp2 p), ∃ d ∈ D,
      d.1 - α ∈ Ideal.span {((p : Zp2 p)) ^ k} ∧ d.2 - β ∈ Ideal.span {((p : Zp2 p)) ^ k})
    (t : ∀ (C : Type u) [CommRing C] [Algebra L C], Ideal C → (Fin 2 → C) → (Fin 2 → C))
    (ht_mem : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → ∀ i, t C J x i ∈ J)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra L C] [CommRing C'] [Algebra L C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[L] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → t C' J' (φ ∘ x) = φ ∘ t C J x)
    (ht_add : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x y : Fin 2 → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J (Sum.elim x y) (X.F.toPowerSeries i)) =
          fun i => MvFormalGroup.adicEval J (Sum.elim (t C J x) (t C J y)) (X'.F.toPowerSeries i))
    (ht_D : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ d ∈ D, ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J x
            (SpecialFormal.Series.addVia X.F (X.act d.1) ((X.act d.2).comp X.varpi) i)) =
          fun i => MvFormalGroup.adicEval J (t C J x)
            (SpecialFormal.Series.addVia X'.F (X'.act d.1) ((X'.act d.2).comp X'.varpi) i)) :
    ∃! u : X.Hom X',
      ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
          ∀ i, t C J x i = MvFormalGroup.adicEval J x (u.toSeries i) := by
  refine CerednikDrinfeld.FormalODModule.existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent X X' t
    ht_mem ht_nat ht_add ?_ ?_
  ·
    intro C _ _ J hJ a x hx
    obtain ⟨K, hK⟩ := exists_forall_adicEval_act_pow_eq_zero hp J hJ
    obtain ⟨d, hdD, hd1, hd2⟩ := hD K a 0
    obtain ⟨γ, hγ⟩ := exists_eq_add_pow_mul hd1
    obtain ⟨δ, hδ⟩ := exists_eq_add_pow_mul hd2
    rw [zero_add] at hδ
    have key := ht_D C J hJ d hdD x hx
    rwa [adicEval_addVia_eq_act X J hJ (hK X) a d.1 d.2 γ δ hγ hδ hx,
      adicEval_addVia_eq_act X' J hJ (hK X') a d.1 d.2 γ δ hγ hδ (ht_mem C J hJ x hx)] at key
  ·
    intro C _ _ J hJ x hx
    obtain ⟨K, hK⟩ := exists_forall_adicEval_act_pow_eq_zero hp J hJ
    obtain ⟨d, hdD, hd1, hd2⟩ := hD K 0 1
    obtain ⟨γ, hγ⟩ := exists_eq_add_pow_mul hd1
    obtain ⟨δ, hδ⟩ := exists_eq_add_pow_mul hd2
    rw [zero_add] at hγ
    have key := ht_D C J hJ d hdD x hx
    rwa [adicEval_addVia_eq_varpi X J hJ (hK X) d.1 d.2 γ δ hγ hδ hx,
      adicEval_addVia_eq_varpi X' J hJ (hK X') d.1 d.2 γ δ hγ hδ (ht_mem C J hJ x hx)] at key

end Main

end CerednikDrinfeld.FormalODModule.NilDenseEquiv

open CerednikDrinfeld.FormalODModule.NilDenseEquiv in
theorem solution
    {p : ℕ} [Fact p.Prime] {L : Type u} [CommRing L] (hp : IsNilpotent (p : L))
    (X X' : CerednikDrinfeld.FormalODModule p L)
    (D : Set (CerednikDrinfeld.Zp2 p × CerednikDrinfeld.Zp2 p))
    (hD : ∀ (k : ℕ) (α β : CerednikDrinfeld.Zp2 p), ∃ d ∈ D,
      d.1 - α ∈ Ideal.span {((p : CerednikDrinfeld.Zp2 p)) ^ k} ∧
        d.2 - β ∈ Ideal.span {((p : CerednikDrinfeld.Zp2 p)) ^ k})
    (t : ∀ (C : Type u) [CommRing C] [Algebra L C], Ideal C → (Fin 2 → C) → (Fin 2 → C))
    (ht_mem : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → ∀ i, t C J x i ∈ J)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra L C] [CommRing C'] [Algebra L C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[L] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → t C' J' (φ ∘ x) = φ ∘ t C J x)
    (ht_add : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x y : Fin 2 → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J (Sum.elim x y) (X.F.toPowerSeries i)) =
          fun i => MvFormalGroup.adicEval J (Sum.elim (t C J x) (t C J y)) (X'.F.toPowerSeries i))
    (ht_D : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ d ∈ D, ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J x
            (CerednikDrinfeld.SpecialFormal.Series.addVia X.F (X.act d.1) ((X.act d.2).comp X.varpi) i)) =
          fun i => MvFormalGroup.adicEval J (t C J x)
            (CerednikDrinfeld.SpecialFormal.Series.addVia X'.F (X'.act d.1) ((X'.act d.2).comp X'.varpi) i)) :
    ∃! u : X.Hom X',
      ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
          ∀ i, t C J x i = MvFormalGroup.adicEval J x (u.toSeries i) :=
  existsUnique_odHom_of_dense hp X X' D hD t ht_mem ht_nat ht_add ht_D

end S_CerednikDrinfeld_FormalODModule_existsUnique_hom_apply_eq_adicEval_of_natural_of_dense_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_hom_apply_eq_adicEval_of_natural_of_dense_of_isNilpotent (solution)
