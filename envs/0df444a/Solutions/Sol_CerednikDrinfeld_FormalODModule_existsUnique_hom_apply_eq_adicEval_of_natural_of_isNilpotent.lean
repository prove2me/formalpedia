-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e6995c8f-85a5-52aa-bd49-9eb6bf9a0733

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent

set_option autoImplicit false

open MvPowerSeries

universe u v w z

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 SpecialFormal.Series SpecialFormal.Series.comp SpecialFormal.IsLawHom SpecialFormal.IsLawHom.of_hom FormalODModule FormalODModule.Hom FormalODModule.Hom.ext"
namespace FormalODModule
p2m_export "CerednikDrinfeld.FormalODModule" "actEnd varpiEnd Hom Hom.ext Hom.comp F varpi act"
namespace NilYonedaODHom
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

theorem map_adicEval [Finite σ] {C' : Type z} [CommRing C'] [Algebra R C'] (J : Ideal C) (J' : Ideal C')
    (hJ : IsNilpotent J) (hJ' : IsNilpotent J') (φ : C →ₐ[R] C') {x : σ → C} (hx : ∀ s, x s ∈ J)
    (hx' : ∀ s, φ (x s) ∈ J') (f : MvPowerSeries σ R) :
    φ (MvFormalGroup.adicEval J x f) = MvFormalGroup.adicEval J' (fun s => φ (x s)) f := by
  classical
  haveI := Fintype.ofFinite σ
  obtain ⟨N, hN⟩ := hJ
  obtain ⟨N', hN'⟩ := hJ'
  have hM : J ^ max N N' = ⊥ := by
    rw [show max N N' = N + (max N N' - N) by omega, pow_add, hN, zero_mul]; rfl
  have hM' : J' ^ max N N' = ⊥ := by
    rw [show max N N' = N' + (max N N' - N') by omega, pow_add, hN', zero_mul]; rfl
  rw [adicEval_eq_sum J hM hx f _ (le_degree_of_not_mem_Iic (max N N')),
    adicEval_eq_sum J' hM' hx' f _ (le_degree_of_not_mem_Iic (max N N'))]
  simp only [map_sum, map_mul, AlgHom.commutes, Finsupp.prod, map_prod, map_pow]

end Engine

section EvalFam

variable {L : Type u} [CommRing L] {d h : ℕ} {F : MvFormalGroup d L} {G : MvFormalGroup h L}

noncomputable def evalFam (η : MvFormalGroup.Hom F G) :
    ∀ (C : Type u) [CommRing C] [Algebra L C], Ideal C → (Fin d → C) → (Fin h → C) :=
  fun _ _ _ J x i => MvFormalGroup.adicEval J x (η.toPowerSeries i)

theorem evalFam_apply (η : MvFormalGroup.Hom F G) (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C)
    (x : Fin d → C) (i : Fin h) : evalFam η C J x i = MvFormalGroup.adicEval J x (η.toPowerSeries i) := rfl

theorem evalFam_mem (η : MvFormalGroup.Hom F G) :
    ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin d → C, (∀ j, x j ∈ J) → ∀ i, evalFam η C J x i ∈ J :=
  fun _ _ _ J hJ _ hx i => adicEval_mem J hJ hx (η.constantCoeff_eq_zero i)

theorem evalFam_nat (η : MvFormalGroup.Hom F G) :
    ∀ (C C' : Type u) [CommRing C] [Algebra L C] [CommRing C'] [Algebra L C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[L] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : Fin d → C, (∀ j, x j ∈ J) → evalFam η C' J' (φ ∘ x) = φ ∘ evalFam η C J x := by
  intro C C' _ _ _ _ J J' hJ hJ' φ hφ x hx
  funext i
  exact (map_adicEval J J' hJ hJ' φ hx (fun s => hφ _ (hx s)) (η.toPowerSeries i)).symm

theorem evalFam_add (η : MvFormalGroup.Hom F G) :
    ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
        evalFam η C J (fun i => MvFormalGroup.adicEval J (Sum.elim x y) (F.toPowerSeries i)) =
          fun i => MvFormalGroup.adicEval J (Sum.elim (evalFam η C J x) (evalFam η C J y))
            (G.toPowerSeries i) := by
  intro C _ _ J hJ x y hx hy
  haveI := isAdicComplete_of_isNilpotent J hJ
  let P : F.Points C J := ⟨x, fun j => Ideal.le_radical (hx j)⟩
  let Q : F.Points C J := ⟨y, fun j => Ideal.le_radical (hy j)⟩
  have key := congrArg MvFormalGroup.Points.val (map_add η.evalPoints P Q)
  funext i
  exact congrFun key i

end EvalFam

section Main

variable {p : ℕ} [Fact p.Prime] {L : Type u} [CommRing L]

theorem adicEval_subst_of_isNilpotent {C : Type u} [CommRing C] [Algebra L C] (J : Ideal C)
    (hJ : IsNilpotent J) {x : Fin 2 → C} (hx : ∀ j, x j ∈ J) {φ : SpecialFormal.Series L}
    (hφ : ∀ i, (φ i).constantCoeff = 0) (g : MvPowerSeries (Fin 2) L) :
    MvFormalGroup.adicEval J x (subst φ g) =
      MvFormalGroup.adicEval J (fun j => MvFormalGroup.adicEval J x (φ j)) g := by
  haveI := isAdicComplete_of_isNilpotent J hJ
  exact MvFormalGroup.adicEval_subst J (fun j => Ideal.le_radical (hx j))
    (hasSubst_of_constantCoeff_zero hφ) g

theorem comp_eq_comp_of_intertwines (X X' : FormalODModule p L)
    (t : ∀ (C : Type u) [CommRing C] [Algebra L C], Ideal C → (Fin 2 → C) → (Fin 2 → C))
    (ψ : MvFormalGroup.Hom X.F X'.F)
    (hψ : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → ∀ i, t C J x i = MvFormalGroup.adicEval J x (ψ.toPowerSeries i))
    (α : MvFormalGroup.End X.F) (α' : MvFormalGroup.End X'.F)
    (ht : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J x (α.toPowerSeries i)) =
          fun i => MvFormalGroup.adicEval J (t C J x) (α'.toPowerSeries i)) :
    MvFormalGroup.Hom.comp ψ α = MvFormalGroup.Hom.comp α' ψ := by

  have hEU := MvFormalGroup.existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent X.F X'.F
    (evalFam (MvFormalGroup.Hom.comp ψ α)) (evalFam_mem _) (evalFam_nat _) (evalFam_add _)
  refine hEU.unique (fun _ _ _ _ _ _ _ _ => rfl) ?_
  intro C _ _ J hJ x hx i

  have hαx : ∀ j, MvFormalGroup.adicEval J x (α.toPowerSeries j) ∈ J :=
    fun j => adicEval_mem J hJ hx (α.constantCoeff_eq_zero j)
  have htx : ∀ j, t C J x j ∈ J := by
    intro j
    rw [hψ C J hJ x hx j]
    exact adicEval_mem J hJ hx (ψ.constantCoeff_eq_zero j)
  calc evalFam (MvFormalGroup.Hom.comp ψ α) C J x i
      = MvFormalGroup.adicEval J x (subst α.toPowerSeries (ψ.toPowerSeries i)) := rfl
    _ = MvFormalGroup.adicEval J (fun j => MvFormalGroup.adicEval J x (α.toPowerSeries j))
          (ψ.toPowerSeries i) :=
        adicEval_subst_of_isNilpotent J hJ hx α.constantCoeff_eq_zero _
    _ = t C J (fun j => MvFormalGroup.adicEval J x (α.toPowerSeries j)) i := (hψ C J hJ _ hαx i).symm
    _ = MvFormalGroup.adicEval J (t C J x) (α'.toPowerSeries i) := congrFun (ht C J hJ x hx) i
    _ = MvFormalGroup.adicEval J (fun j => MvFormalGroup.adicEval J x (ψ.toPowerSeries j))
          (α'.toPowerSeries i) := by
        congr 1
        funext j
        exact hψ C J hJ x hx j
    _ = MvFormalGroup.adicEval J x (subst ψ.toPowerSeries (α'.toPowerSeries i)) :=
        (adicEval_subst_of_isNilpotent J hJ hx ψ.constantCoeff_eq_zero _).symm
    _ = MvFormalGroup.adicEval J x ((MvFormalGroup.Hom.comp α' ψ).toPowerSeries i) := rfl

theorem existsUnique_odHom (X X' : FormalODModule p L)
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
    (ht_act : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ (a : Zp2 p) (x : Fin 2 → C), (∀ j, x j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J x (X.act a i)) =
          fun i => MvFormalGroup.adicEval J (t C J x) (X'.act a i))
    (ht_varpi : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J x (X.varpi i)) =
          fun i => MvFormalGroup.adicEval J (t C J x) (X'.varpi i)) :
    ∃! u : X.Hom X',
      ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
          ∀ i, t C J x i = MvFormalGroup.adicEval J x (u.toSeries i) := by

  obtain ⟨ψ, hψ, hψu⟩ := MvFormalGroup.existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent
    X.F X'.F t ht_mem ht_nat ht_add

  have hact : ∀ a, SpecialFormal.Series.comp ψ.toPowerSeries (X.act a) =
      SpecialFormal.Series.comp (X'.act a) ψ.toPowerSeries := by
    intro a
    have key := comp_eq_comp_of_intertwines X X' t ψ hψ (X.actEnd a) (X'.actEnd a)
      (fun C _ _ J hJ x hx => ht_act C J hJ a x hx)
    exact congrArg MvFormalGroup.Hom.toPowerSeries key
  have hvarpi : SpecialFormal.Series.comp ψ.toPowerSeries X.varpi =
      SpecialFormal.Series.comp X'.varpi ψ.toPowerSeries := by
    have key := comp_eq_comp_of_intertwines X X' t ψ hψ X.varpiEnd X'.varpiEnd
      (fun C _ _ J hJ x hx => ht_varpi C J hJ x hx)
    exact congrArg MvFormalGroup.Hom.toPowerSeries key
  let u : X.Hom X' := ⟨ψ.toPowerSeries, SpecialFormal.IsLawHom.of_hom ψ, hact, hvarpi⟩
  refine ⟨u, fun C _ _ J hJ x hx i => hψ C J hJ x hx i, ?_⟩

  intro u' hu'
  have h1 : u'.toLawHom = ψ := hψu u'.toLawHom fun C _ _ J hJ x hx i => hu' C J hJ x hx i
  apply FormalODModule.Hom.ext
  exact congrArg MvFormalGroup.Hom.toPowerSeries h1

end Main

end CerednikDrinfeld.FormalODModule.NilYonedaODHom

open CerednikDrinfeld.FormalODModule.NilYonedaODHom in
theorem solution
    {p : ℕ} [Fact p.Prime] {L : Type u} [CommRing L] (X X' : CerednikDrinfeld.FormalODModule p L)
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
    (ht_act : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ (a : CerednikDrinfeld.Zp2 p) (x : Fin 2 → C), (∀ j, x j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J x (X.act a i)) =
          fun i => MvFormalGroup.adicEval J (t C J x) (X'.act a i))
    (ht_varpi : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J x (X.varpi i)) =
          fun i => MvFormalGroup.adicEval J (t C J x) (X'.varpi i)) :
    ∃! u : X.Hom X',
      ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
          ∀ i, t C J x i = MvFormalGroup.adicEval J x (u.toSeries i) :=
  existsUnique_odHom X X' t ht_mem ht_nat ht_add ht_act ht_varpi

end S_CerednikDrinfeld_FormalODModule_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent (solution)
