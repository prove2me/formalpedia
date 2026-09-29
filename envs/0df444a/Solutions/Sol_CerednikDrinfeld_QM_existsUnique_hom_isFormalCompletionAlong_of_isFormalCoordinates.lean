-- Prove2me | solution 1 for CerednikDrinfeld.QM.existsUnique_hom_isFormalCompletionAlong_of_isFormalCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/85107e94-728b-5e08-8f7e-16249f789bc3

import Mathlib
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Theorems.Thm_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_existsUnique_hom_isFormalCompletionAlong_of_isFormalCoordinates

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_existsUnique_hom_isFormalCompletionAlong_of_isFormalCoordinates.CerednikDrinfeld.QM MvPowerSeries"

universe u v w

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve tree"
namespace QM
p2m_export "CerednikDrinfeld.QM" "mapPt pushPt FakeEllipticCurve IsFormalCompletionAlong"
namespace LawCompletion
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

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

section Generic

variable {B : Type} [CommRing B] {A A' : Scheme.{0}}
  {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)}

theorem schemeHomOverComp_mapPt (h : A ⟶ A') (hh : h ≫ f' = f) {T T' : Scheme.{0}}
    {t : T ⟶ Spec (CommRingCat.of B)} {t' : T' ⟶ Spec (CommRingCat.of B)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (P : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (mapPt h hh P) = mapPt h hh (schemeHomOverComp ψ hψ P) :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem mapPt_pushPt (h : A ⟶ A') (hh : h ≫ f' = f) (φ : A ⟶ A) (hφ : φ ≫ f = f) (φ' : A' ⟶ A')
    (hφ' : φ' ≫ f' = f') (hcomm : φ ≫ h = h ≫ φ') {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)}
    (P : SchemeHomOver t f) :
    mapPt h hh (pushPt φ hφ P) = pushPt φ' hφ' (mapPt h hh P) := by
  apply Subtype.ext
  show (P.1 ≫ φ) ≫ h = (P.1 ≫ h) ≫ φ'
  rw [Category.assoc, hcomm, Category.assoc]

theorem exists_pow_succ_eq_bot {C : Type} [CommRing C] {J : Ideal C} (hJ : IsNilpotent J) :
    ∃ n : ℕ, J ^ (n + 1) = ⊥ := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  rw [pow_succ, hn, zero_mul]
  rfl

theorem isNilpotent_of_pow_succ_eq_bot {C : Type} [CommRing C] {J : Ideal C} {n : ℕ} (hn : J ^ (n + 1) = ⊥) :
    IsNilpotent J :=
  ⟨n + 1, hn⟩

theorem isNilpotent_of_mem {C : Type} [CommRing C] {J : Ideal C} (hJ : IsNilpotent J) {x : C} (hx : x ∈ J) :
    IsNilpotent x := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  have hmem : x ^ n ∈ J ^ n := Ideal.pow_mem_pow hx n
  rw [hn] at hmem
  exact (Submodule.mem_bot C).mp hmem

end Generic

section Transport

variable {B : Type} [CommRing B] {A A' : Scheme.{0}}
  {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)} {g g' : ℕ}
  {L : RelativeGroupLaw B f} {L' : RelativeGroupLaw B f'} {F : MvFormalGroup g B} {F' : MvFormalGroup g' B}
  {θ : RelativeGroupLaw.FormalCoordinates f g} {θ' : RelativeGroupLaw.FormalCoordinates f' g'}
  {h : A ⟶ A'} {hh : h ≫ f' = f}

def IsPointHom (L : RelativeGroupLaw B f) (L' : RelativeGroupLaw B f') (h : A ⟶ A') (hh : h ≫ f' = f) : Prop :=
  ∀ (B' : Type) [CommRing B'] [Algebra B B'] (P Q : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f),
    mapPt h hh (L.mul (Scheme.specOver (𝒪 := B) B') P Q) =
      L'.mul (Scheme.specOver (𝒪 := B) B') (mapPt h hh P) (mapPt h hh Q)

theorem mapPt_one_specOver (hmul : IsPointHom L L' h hh) (C : Type) [CommRing C] [Algebra B C] :
    mapPt h hh (L.one (Scheme.specOver (𝒪 := B) C)) = L'.one (Scheme.specOver (𝒪 := B) C) := by
  letI := L'.pointGroup (Scheme.specOver (𝒪 := B) C)
  have key : mapPt h hh (L.one _) * mapPt h hh (L.one _) = mapPt h hh (L.one (Scheme.specOver (𝒪 := B) C)) := by
    show L'.mul _ _ _ = _
    rw [← hmul, L.one_mul]
  exact mul_eq_left.mp key

theorem isInfinitesimal_mapPt (hθ : L.IsFormalCoordinates F θ) (hmul : IsPointHom L L' h hh)
    {C : Type} [CommRing C] [Algebra B C] (J : Ideal C) {n : ℕ} (hn : J ^ (n + 1) = ⊥)
    (x : Fin g → C) (hx : ∀ j, x j ∈ J) :
    L'.IsInfinitesimal J (mapPt h hh (θ C x)) := by
  have hP : L.IsInfinitesimal J (θ C x) := (hθ.2 C J n hn).1 x hx
  unfold RelativeGroupLaw.IsInfinitesimal at hP ⊢
  rw [schemeHomOverComp_mapPt, hP, mapPt_one_specOver hmul]

theorem exists_transport (hθ : L.IsFormalCoordinates F θ) (hθ' : L'.IsFormalCoordinates F' θ')
    (hmul : IsPointHom L L' h hh)
    {C : Type} [CommRing C] [Algebra B C] (J : Ideal C) (hJ : IsNilpotent J)
    (x : Fin g → C) (hx : ∀ j, x j ∈ J) :
    ∃ s : Fin g' → C, (∀ j, s j ∈ J) ∧ θ' C s = mapPt h hh (θ C x) := by
  obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
  exact (hθ'.2 C J n hn).2.2.1 _ (isInfinitesimal_mapPt hθ hmul J hn x hx)

noncomputable def transport (hθ : L.IsFormalCoordinates F θ) (hθ' : L'.IsFormalCoordinates F' θ')
    (hmul : IsPointHom L L' h hh) :
    ∀ (C : Type) [CommRing C] [Algebra B C], Ideal C → (Fin g → C) → (Fin g' → C) :=
  fun C _ _ J x => by
    classical
    exact if hJx : IsNilpotent J ∧ ∀ j, x j ∈ J then
      Classical.choose (exists_transport hθ hθ' hmul J hJx.1 x hJx.2) else fun _ => 0

theorem transport_spec (hθ : L.IsFormalCoordinates F θ) (hθ' : L'.IsFormalCoordinates F' θ')
    (hmul : IsPointHom L L' h hh)
    {C : Type} [CommRing C] [Algebra B C] (J : Ideal C) (hJ : IsNilpotent J)
    (x : Fin g → C) (hx : ∀ j, x j ∈ J) :
    (∀ j, transport hθ hθ' hmul C J x j ∈ J) ∧ θ' C (transport hθ hθ' hmul C J x) = mapPt h hh (θ C x) := by
  classical
  have hdef : transport hθ hθ' hmul C J x =
      Classical.choose (exists_transport hθ hθ' hmul J hJ x hx) := by
    unfold transport
    rw [dif_pos ⟨hJ, hx⟩]
  rw [hdef]
  exact Classical.choose_spec (exists_transport hθ hθ' hmul J hJ x hx)

theorem eq_transport (hθ : L.IsFormalCoordinates F θ) (hθ' : L'.IsFormalCoordinates F' θ')
    (hmul : IsPointHom L L' h hh)
    {C : Type} [CommRing C] [Algebra B C] (J : Ideal C) (hJ : IsNilpotent J)
    (x : Fin g → C) (hx : ∀ j, x j ∈ J) (s : Fin g' → C) (hs : ∀ j, s j ∈ J)
    (hθs : θ' C s = mapPt h hh (θ C x)) : s = transport hθ hθ' hmul C J x := by
  obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
  have hsp := transport_spec hθ hθ' hmul J hJ x hx
  exact (hθ'.2 C J n hn).2.1 s _ hs hsp.1 (hθs.trans hsp.2.symm)

theorem transport_nat (hθ : L.IsFormalCoordinates F θ) (hθ' : L'.IsFormalCoordinates F' θ')
    (hmul : IsPointHom L L' h hh) :
    ∀ (C C' : Type) [CommRing C] [Algebra B C] [CommRing C'] [Algebra B C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[B] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : Fin g → C, (∀ j, x j ∈ J) →
          transport hθ hθ' hmul C' J' (φ ∘ x) = φ ∘ transport hθ hθ' hmul C J x := by
  intro C C' _ _ _ _ J J' hJ hJ' φ hφ x hx
  have hsp := transport_spec hθ hθ' hmul J hJ x hx
  symm
  refine eq_transport hθ hθ' hmul J' hJ' (φ ∘ x) (fun j => hφ _ (hx j)) _ (fun j => hφ _ (hsp.1 j)) ?_
  have hnil : ∀ i, IsNilpotent (transport hθ hθ' hmul C J x i) := fun i => isNilpotent_of_mem hJ (hsp.1 i)
  have hnilx : ∀ i, IsNilpotent (x i) := fun i => isNilpotent_of_mem hJ (hx i)
  rw [hθ'.1 C C' φ _ hnil, hsp.2, schemeHomOverComp_mapPt, ← hθ.1 C C' φ x hnilx]

theorem transport_add (hθ : L.IsFormalCoordinates F θ) (hθ' : L'.IsFormalCoordinates F' θ')
    (hmul : IsPointHom L L' h hh) :
    ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
      ∀ x y : Fin g → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
        transport hθ hθ' hmul C J (fun i => MvFormalGroup.adicEval J (Sum.elim x y) (F.toPowerSeries i)) =
          fun i => MvFormalGroup.adicEval J
            (Sum.elim (transport hθ hθ' hmul C J x) (transport hθ hθ' hmul C J y)) (F'.toPowerSeries i) := by
  intro C _ _ J hJ x y hx hy
  obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
  have hspx := transport_spec hθ hθ' hmul J hJ x hx
  have hspy := transport_spec hθ hθ' hmul J hJ y hy
  set tx := transport hθ hθ' hmul C J x with htx
  set ty := transport hθ hθ' hmul C J y with hty
  have hxy : ∀ j, Sum.elim x y j ∈ J := by
    rintro (j | j)
    exacts [hx j, hy j]
  have htxy : ∀ j, Sum.elim tx ty j ∈ J := by
    rintro (j | j)
    exacts [hspx.1 j, hspy.1 j]
  have e1 : (fun i => MvFormalGroup.adicEval J (Sum.elim x y) (F.toPowerSeries i)) = F.nilMul n x y :=
    funext fun i => (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ hxy).symm
  have e2 : (fun i => MvFormalGroup.adicEval J (Sum.elim tx ty) (F'.toPowerSeries i)) = F'.nilMul n tx ty :=
    funext fun i => (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ htxy).symm
  have hmem1 : ∀ j, F.nilMul n x y j ∈ J := by
    intro j
    rw [← congrFun e1 j]
    exact adicEval_mem J hJ hxy (F.constantCoeff_eq_zero j)
  have hmem2 : ∀ j, F'.nilMul n tx ty j ∈ J := by
    intro j
    rw [← congrFun e2 j]
    exact adicEval_mem J hJ htxy (F'.constantCoeff_eq_zero j)
  rw [e1, e2]
  symm
  refine eq_transport hθ hθ' hmul J hJ _ hmem1 _ hmem2 ?_
  rw [(hθ'.2 C J n hn).2.2.2 tx ty hspx.1 hspy.1, hspx.2, hspy.2, ← hmul,
    ← (hθ.2 C J n hn).2.2.2 x y hx hy]

end Transport

section Main

variable {B : Type} [CommRing B] {A A' : Scheme.{0}}
  {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)} {g g' : ℕ}

theorem existsUnique_completion (L : RelativeGroupLaw B f) (L' : RelativeGroupLaw B f')
    (F : MvFormalGroup g B) (F' : MvFormalGroup g' B)
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f' g')
    (hθ : L.IsFormalCoordinates F θ) (hθ' : L'.IsFormalCoordinates F' θ')
    (h : A ⟶ A') (hh : h ≫ f' = f) (hmul : IsPointHom L L' h hh) :
    ∃! φ : MvFormalGroup.Hom F F', IsFormalCompletionAlong θ θ' h hh φ.toPowerSeries := by

  obtain ⟨u, hu, huniq⟩ :=
    MvFormalGroup.existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent F F'
      (transport hθ hθ' hmul)
      (fun C _ _ J hJ x hx => (transport_spec hθ hθ' hmul J hJ x hx).1)
      (transport_nat hθ hθ' hmul) (transport_add hθ hθ' hmul)
  refine ⟨u, ?_, ?_⟩
  ·
    intro C _ _ J n hn s hs
    have hJ : IsNilpotent J := isNilpotent_of_pow_succ_eq_bot hn
    have hsp := transport_spec hθ hθ' hmul J hJ s hs
    have e : (fun i => MvFormalGroup.nilEval n (u.toPowerSeries i) s) = transport hθ hθ' hmul C J s := by
      funext i
      rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ hs]
      exact (hu C J hJ s hs i).symm
    rw [e, hsp.2]
  ·
    intro u' hu'
    apply huniq
    intro C _ _ J hJ x hx i
    obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
    have key := hu' C J n hn x hx
    have hmem : ∀ j, MvFormalGroup.nilEval n (u'.toPowerSeries j) x ∈ J := by
      intro j
      rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ hx]
      exact adicEval_mem J hJ hx (u'.constantCoeff_eq_zero j)
    have heq := eq_transport hθ hθ' hmul J hJ x hx _ hmem key
    rw [← congrFun heq i]
    exact MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ hx

end Main

end CerednikDrinfeld.QM.LawCompletion

open CerednikDrinfeld.QM.LawCompletion in
theorem solution
    {B : Type} [CommRing B] {A A' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)} {g g' : ℕ}
    (L : RelativeGroupLaw B f) (L' : RelativeGroupLaw B f')
    (F : MvFormalGroup g B) (F' : MvFormalGroup g' B)
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f' g')
    (hθ : L.IsFormalCoordinates F θ) (hθ' : L'.IsFormalCoordinates F' θ')
    (h : A ⟶ A') (hh : h ≫ f' = f)
    (hmul : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (P Q : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f),
      mapPt h hh (L.mul (Scheme.specOver (𝒪 := B) B') P Q) =
        L'.mul (Scheme.specOver (𝒪 := B) B') (mapPt h hh P) (mapPt h hh Q)) :
    ∃! φ : MvFormalGroup.Hom F F', IsFormalCompletionAlong θ θ' h hh φ.toPowerSeries :=
  existsUnique_completion L L' F F' θ θ' hθ hθ' h hh hmul

end S_CerednikDrinfeld_QM_existsUnique_hom_isFormalCompletionAlong_of_isFormalCoordinates
end P2MW
export P2MW.S_CerednikDrinfeld_QM_existsUnique_hom_isFormalCompletionAlong_of_isFormalCoordinates (solution)
