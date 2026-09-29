-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isOpen_forall_lattice_eq_or_bijective_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0e90d9c8-f4bb-5063-9cbb-3f3669c5b5f4

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isOpen_forall_lattice_eq_or_bijective_map

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega TensorProduct

noncomputable section

namespace P2mKcQuadrupleTypes

section Strata

variable {R : Type} [CommRing R] {P Q : Type} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

theorem map_mem_of_mem_smul_top (I : Ideal R) (φ : Q →ₗ[R] R) {q : Q} (hq : q ∈ (I • ⊤ : Submodule R Q)) : φ q ∈ I := by
  induction hq using Submodule.smul_induction_on' with
  | smul r hr n _ => rw [map_smul, smul_eq_mul]; exact I.mul_mem_right _ hr
  | add a b _ _ ha hb => rw [map_add]; exact I.add_mem ha hb

theorem mem_smul_top_iff_forall [Module.Projective R Q] (I : Ideal R) (q : Q) :
    q ∈ (I • ⊤ : Submodule R Q) ↔ ∀ φ : Q →ₗ[R] R, φ q ∈ I := by
  refine ⟨fun hq φ => map_mem_of_mem_smul_top I φ hq, fun h => ?_⟩
  by_contra hq
  obtain ⟨φ, hφ⟩ := exists_linearMap_apply_not_mem I q hq
  exact hφ (h φ)

theorem isClosed_setOf_range_le [Module.Projective R Q] (f : P →ₗ[R] Q) :
    IsClosed {y : PrimeSpectrum R | LinearMap.range f ≤ y.asIdeal • (⊤ : Submodule R Q)} := by
  have h : {y : PrimeSpectrum R | LinearMap.range f ≤ y.asIdeal • (⊤ : Submodule R Q)} =
      PrimeSpectrum.zeroLocus (Set.range fun pφ : P × (Q →ₗ[R] R) => pφ.2 (f pφ.1)) := by
    ext y
    rw [Set.mem_setOf_eq, PrimeSpectrum.mem_zeroLocus, Set.range_subset_iff]
    constructor
    · rintro hle ⟨p, φ⟩
      exact (mem_smul_top_iff_forall _ _).mp (hle ⟨p, rfl⟩) φ
    · rintro h _ ⟨p, rfl⟩
      exact (mem_smul_top_iff_forall _ _).mpr fun φ => h ⟨p, φ⟩
  rw [h]
  exact PrimeSpectrum.isClosed_zeroLocus _

end Strata

section Stalk

variable {R : Type} [CommRing R] {P Q : Type} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

theorem eq_top_of_mem_of_forall_not_mem_smul_top [Module.Invertible R Q] (N : Submodule R Q) (q : Q)
    (hqN : q ∈ N) (hq : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → q ∉ (𝔪 • ⊤ : Submodule R Q)) : N = ⊤ := by
  set A : Ideal R := N.colon (Set.univ : Set Q) with hA_def
  by_cases hA : A = ⊤
  · have h1 : (1 : R) ∈ A := by rw [hA]; exact Submodule.mem_top
    rw [hA_def, Submodule.mem_colon] at h1
    refine eq_top_iff.mpr fun m _ => ?_
    have := h1 m (Set.mem_univ m)
    rwa [one_smul] at this
  · exfalso
    obtain ⟨𝔪, h𝔪, hA𝔪⟩ := Ideal.exists_le_maximal A hA
    obtain ⟨φ, hφ⟩ := exists_linearMap_apply_not_mem 𝔪 q (hq 𝔪 h𝔪)
    obtain ⟨c, hc⟩ := (Module.Invertible.toModuleEnd_bijective R Q).2 (LinearMap.smulRight φ q)
    have hc' : ∀ x : Q, c • x = φ x • q := fun x => by
      have := congrArg (fun f : Module.End R Q => f x) hc
      simp only [LinearMap.smulRight_apply] at this
      exact this
    have hcA : c ∈ A := by
      rw [hA_def, Submodule.mem_colon]
      intro m _
      rw [hc' m]
      exact N.smul_mem _ hqN
    have hkey : (φ q - c) * φ q = 0 := by
      have h := congrArg φ (hc' q)
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
      rw [sub_mul, ← h, sub_self]
    have hmem : (φ q - c) * φ q ∈ 𝔪 := by rw [hkey]; exact 𝔪.zero_mem
    rcases h𝔪.isPrime.mem_or_mem hmem with h1 | h1
    · apply hφ
      have : φ q = (φ q - c) + c := by ring
      rw [this]
      exact 𝔪.add_mem h1 (hA𝔪 hcA)
    · exact hφ h1

theorem mem_ideal_smul_top_of_mem_maximalIdeal_smul_top (y : PrimeSpectrum R) (q : LocalizedModule y.asIdeal.primeCompl Q)
    (hq : q ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime y.asIdeal) • ⊤ :
      Submodule (Localization.AtPrime y.asIdeal) (LocalizedModule y.asIdeal.primeCompl Q))) :
    q ∈ (y.asIdeal • ⊤ : Submodule R (LocalizedModule y.asIdeal.primeCompl Q)) := by
  induction hq using Submodule.smul_induction_on' with
  | smul r hr t _ =>
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective y.asIdeal.primeCompl r
    have hb : b ∈ y.asIdeal := (IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime y.asIdeal) y.asIdeal b s).mp hr
    have e : IsLocalization.mk' (Localization.AtPrime y.asIdeal) b s • t =
        b • (IsLocalization.mk' (Localization.AtPrime y.asIdeal) (1 : R) s • t) := by
      rw [← smul_assoc, Algebra.smul_def b (IsLocalization.mk' (Localization.AtPrime y.asIdeal) (1 : R) s),
        ← IsLocalization.mk'_eq_mul_mk'_one]
    rw [e]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb

theorem mk_not_mem_maximalIdeal_smul_top [Module.Projective R Q] (y : PrimeSpectrum R) (q : Q)
    (hq : q ∉ (y.asIdeal • ⊤ : Submodule R Q)) :
    LocalizedModule.mk q (1 : y.asIdeal.primeCompl) ∉
      (IsLocalRing.maximalIdeal (Localization.AtPrime y.asIdeal) • ⊤ :
        Submodule (Localization.AtPrime y.asIdeal) (LocalizedModule y.asIdeal.primeCompl Q)) := by
  intro hmem
  obtain ⟨φ, hφ⟩ := exists_linearMap_apply_not_mem y.asIdeal q hq
  have h1 := mem_ideal_smul_top_of_mem_maximalIdeal_smul_top y _ hmem

  have h2 : (y.asIdeal • ⊤ : Submodule R (LocalizedModule y.asIdeal.primeCompl Q)) =
      (y.asIdeal • (⊤ : Submodule R Q)).localized₀ y.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap y.asIdeal.primeCompl Q) := by
    rw [Submodule.localized₀_smul, Submodule.localized₀_top]
  rw [h2, Submodule.mem_localized₀] at h1
  obtain ⟨n, hn, s, hs⟩ := h1
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_eq_mk'_iff] at hs
  obtain ⟨c, hc⟩ := hs

  rw [one_smul, Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def, smul_smul] at hc
  have h3 : ((c : R) * s) • q ∈ (y.asIdeal • ⊤ : Submodule R Q) := by rw [hc]; exact Submodule.smul_mem _ _ hn
  have h4 := map_mem_of_mem_smul_top y.asIdeal φ h3
  rw [map_smul, smul_eq_mul] at h4
  rcases y.2.mem_or_mem h4 with h5 | h5
  · rcases y.2.mem_or_mem h5 with h6 | h6
    · exact c.2 h6
    · exact s.2 h6
  · exact hφ h5

theorem bijective_map_of_not_range_le [Module.Invertible R P] [Module.Invertible R Q] (f : P →ₗ[R] Q)
    (y : PrimeSpectrum R) (hy : ¬ LinearMap.range f ≤ y.asIdeal • (⊤ : Submodule R Q)) :
    Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl f) := by
  obtain ⟨p, hp⟩ : ∃ p : P, f p ∉ (y.asIdeal • ⊤ : Submodule R Q) := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hy fun q ⟨p, hpq⟩ => hpq ▸ h p
  apply Module.Invertible.bijective_of_surjective
  rw [← LinearMap.range_eq_top]
  apply eq_top_of_mem_of_forall_not_mem_smul_top _ (LocalizedModule.mk (f p) 1)
    (LinearMap.mem_range.mpr ⟨LocalizedModule.mk p 1, LocalizedModule.map_mk _ f p 1⟩)
  intro 𝔪 h𝔪
  rw [IsLocalRing.eq_maximalIdeal h𝔪]
  exact mk_not_mem_maximalIdeal_smul_top y (f p) hp

theorem mem_smul_top_of_map_mem {A : Type} [CommRing A] {V W : Type} [AddCommGroup V] [Module A V] [AddCommGroup W]
    [Module A W] (g : V →ₗ[A] W) (hg : Function.Bijective g) (I : Ideal A) (m : V)
    (hm : g m ∈ (I • ⊤ : Submodule A W)) : m ∈ (I • ⊤ : Submodule A V) := by
  let e : V ≃ₗ[A] W := LinearEquiv.ofBijective g hg
  have h1 : (I • ⊤ : Submodule A W) = (I • ⊤ : Submodule A V).map e.toLinearMap := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  have h2 : g m = e m := rfl
  rw [h1, h2] at hm
  obtain ⟨m', hm', he⟩ := hm
  rw [LinearEquiv.coe_coe, e.injective.eq_iff] at he
  rwa [← he]

end Stalk

section Cover

variable {R : Type} [CommRing R] {P Q : Type} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

theorem nontrivial_of_invertible [Nontrivial R] [Module.Invertible R P] : Nontrivial P := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : (0 : R) = 1 := FaithfulSMul.eq_of_smul_eq_smul (M := R) (α := P) fun m => Subsingleton.elim _ _
  exact zero_ne_one this

theorem range_le_or_range_le [Module.Invertible R P] [Module.Invertible R Q] (f₀ : P →ₗ[R] Q) (f₁ : Q →ₗ[R] P)
    (a : R) (ha : IsNilpotent a) (h : ∀ t, f₁ (f₀ t) = a • t) (y : PrimeSpectrum R) :
    LinearMap.range f₀ ≤ y.asIdeal • (⊤ : Submodule R Q) ∨ LinearMap.range f₁ ≤ y.asIdeal • (⊤ : Submodule R P) := by
  by_contra hcon
  rw [not_or] at hcon
  have h₀ := (bijective_map_of_not_range_le f₀ y hcon.1).2
  have h₁ := (bijective_map_of_not_range_le f₁ y hcon.2).2
  set S := y.asIdeal.primeCompl

  have hcomp : ∀ m : LocalizedModule S P,
      LocalizedModule.map S f₁ (LocalizedModule.map S f₀ m) = a • m := by
    intro m
    induction m using LocalizedModule.induction_on with
    | h t s => rw [LocalizedModule.map_mk, LocalizedModule.map_mk, h, LocalizedModule.smul'_mk]
  have hsa : Function.Surjective fun m : LocalizedModule S P => a • m := by
    intro m
    obtain ⟨m₁, rfl⟩ := h₁ m
    obtain ⟨m₀, rfl⟩ := h₀ m₁
    exact ⟨m₀, (hcomp m₀).symm⟩
  have hsan : ∀ n : ℕ, Function.Surjective fun m : LocalizedModule S P => a ^ n • m := by
    intro n
    induction n with
    | zero => intro m; exact ⟨m, by simp⟩
    | succ n ih =>
      intro m
      obtain ⟨m₁, rfl⟩ := ih m
      obtain ⟨m₂, rfl⟩ := hsa m₁
      exact ⟨m₂, by simp only [pow_succ, mul_smul]⟩
  obtain ⟨n, hn⟩ := ha
  haveI : Nontrivial (LocalizedModule S P) := nontrivial_of_invertible (R := Localization.AtPrime y.asIdeal)
  obtain ⟨m, hm⟩ := exists_ne (0 : LocalizedModule S P)
  obtain ⟨m', hm'⟩ := hsan n m
  apply hm
  rw [← hm']
  show a ^ n • m' = 0
  rw [hn, zero_smul]

end Cover

section Quadruple

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem mem_stratum₀_or_mem_stratum₁ (hB : IsNilpotent (algebraMap 𝒪 B π)) (Q : DrinfeldDatum (K := K) π B)
    (y : PrimeSpectrum B) : y ∈ Q.stratum₀ ∨ y ∈ Q.stratum₁ :=
  range_le_or_range_le Q.Pi₀ Q.Pi₁ (algebraMap 𝒪 B π) hB Q.Pi₁_Pi₀ y

theorem exists_isOpen_N₀_eq (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, y ∈ Q.stratum₀ → Q.N₀ y = Q.N₀ x := by
  by_cases hx : x ∈ Q.stratum₀
  · exact Q.locallyConstant₀ x hx
  · exact ⟨Q.stratum₀ᶜ, (isClosed_setOf_range_le Q.Pi₀).isOpen_compl, hx, fun y hy hy' => (hy hy').elim⟩

theorem exists_isOpen_N₁_eq (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, y ∈ Q.stratum₁ → Q.N₁ y = Q.N₁ x := by
  by_cases hx : x ∈ Q.stratum₁
  · exact Q.locallyConstant₁ x hx
  · exact ⟨Q.stratum₁ᶜ, (isClosed_setOf_range_le Q.Pi₁).isOpen_compl, hx, fun y hy hy' => (hy hy').elim⟩

theorem N₀_eq_N₁_of_not_mem (Q : DrinfeldDatum (K := K) π B) (y : PrimeSpectrum B) (hy : y ∉ Q.stratum₀) :
    Q.N₀ y = Q.N₁ y := by
  refine le_antisymm (Q.le y) fun v hv => ?_
  have hsurj := (bijective_map_of_not_range_le Q.Pi₀ y hy).2
  apply Q.injective₁ y ⟨v, hv⟩
  refine Submodule.mem_sup_left ?_
  rw [Submodule.restrictScalars_mem, LinearMap.range_eq_top.mpr hsurj]
  exact Submodule.mem_top

theorem exists_eq_smul_of_not_mem (Q : DrinfeldDatum (K := K) π B) (y : PrimeSpectrum B) (hy : y ∉ Q.stratum₁)
    (v : Fin 2 → K) (hv : v ∈ Q.N₀ y) : ∃ w ∈ Q.N₁ y, v = algebraMap 𝒪 K π • w := by
  have hsurj := (bijective_map_of_not_range_le Q.Pi₁ y hy).2
  apply Q.injective₀ y ⟨v, hv⟩
  refine Submodule.mem_sup_left ?_
  rw [Submodule.restrictScalars_mem, LinearMap.range_eq_top.mpr hsurj]
  exact Submodule.mem_top

theorem main (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π))
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      Q.N₀ x ≤ Q.N₀ y ∧ Q.N₁ x ≤ Q.N₁ y ∧
      ((Q.N₀ y = Q.N₀ x ∧ Q.N₁ y = Q.N₁ x) ∨
       (Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl Q.Pi₀) ∧
          Q.N₀ y = Q.N₁ x ∧ Q.N₁ y = Q.N₁ x) ∨
       (Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl Q.Pi₁) ∧
          Q.N₀ y = Q.N₀ x ∧ ∀ v : Fin 2 → K, v ∈ Q.N₁ y ↔ algebraMap 𝒪 K π • v ∈ Q.N₀ x)) := by
  obtain ⟨U₀, hU₀, hx₀, h₀⟩ := exists_isOpen_N₀_eq Q x
  obtain ⟨U₁, hU₁, hx₁, h₁⟩ := exists_isOpen_N₁_eq Q x
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun h =>
    hπ.ne_zero ((injective_iff_map_eq_zero (algebraMap 𝒪 K)).mp (IsFractionRing.injective 𝒪 K) π h)

  have key : ∀ y ∈ U₀ ∩ U₁,
      (Q.N₀ y = Q.N₀ x ∧ Q.N₁ y = Q.N₁ x) ∨
       (Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl Q.Pi₀) ∧
          Q.N₀ y = Q.N₁ x ∧ Q.N₁ y = Q.N₁ x) ∨
       (Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl Q.Pi₁) ∧
          Q.N₀ y = Q.N₀ x ∧ ∀ v : Fin 2 → K, v ∈ Q.N₁ y ↔ algebraMap 𝒪 K π • v ∈ Q.N₀ x) := by
    rintro y ⟨hy₀, hy₁⟩
    by_cases hS₀ : y ∈ Q.stratum₀
    · by_cases hS₁ : y ∈ Q.stratum₁
      · exact Or.inl ⟨h₀ y hy₀ hS₀, h₁ y hy₁ hS₁⟩
      · refine Or.inr (Or.inr ⟨bijective_map_of_not_range_le Q.Pi₁ y hS₁, h₀ y hy₀ hS₀, fun v => ?_⟩)
        rw [← h₀ y hy₀ hS₀]
        constructor
        · exact fun hv => Q.smul_le y v hv
        · intro hv
          obtain ⟨w, hw, hvw⟩ := exists_eq_smul_of_not_mem Q y hS₁ _ hv
          have : v = w := smul_right_injective (Fin 2 → K) hπK hvw
          rwa [this]
    · have hS₁ : y ∈ Q.stratum₁ := (mem_stratum₀_or_mem_stratum₁ hB Q y).resolve_left hS₀
      have e₁ := h₁ y hy₁ hS₁
      exact Or.inr (Or.inl ⟨bijective_map_of_not_range_le Q.Pi₀ y hS₀, (N₀_eq_N₁_of_not_mem Q y hS₀).trans e₁, e₁⟩)
  refine ⟨U₀ ∩ U₁, hU₀.inter hU₁, ⟨hx₀, hx₁⟩, fun y hy => ⟨?_, ?_, key y hy⟩⟩
  · rcases key y hy with h | h | h
    · exact h.1.ge
    · rw [h.2.1]; exact Q.le x
    · exact h.2.1.ge
  · rcases key y hy with h | h | h
    · exact h.2.ge
    · exact h.2.2.ge
    · intro v hv
      exact (h.2.2 v).mpr (Q.smul_le x v hv)

end Quadruple

end P2mKcQuadrupleTypes

end

open P2mKcQuadrupleTypes in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      Q.N₀ x ≤ Q.N₀ y ∧ Q.N₁ x ≤ Q.N₁ y ∧
      ((Q.N₀ y = Q.N₀ x ∧ Q.N₁ y = Q.N₁ x) ∨
       (Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl Q.Pi₀) ∧
          Q.N₀ y = Q.N₁ x ∧ Q.N₁ y = Q.N₁ x) ∨
       (Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl Q.Pi₁) ∧
          Q.N₀ y = Q.N₀ x ∧ ∀ v : Fin 2 → K, v ∈ Q.N₁ y ↔ algebraMap 𝒪 K π • v ∈ Q.N₀ x)) :=
  main hπ hB Q x

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isOpen_forall_lattice_eq_or_bijective_map
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isOpen_forall_lattice_eq_or_bijective_map (solution)
