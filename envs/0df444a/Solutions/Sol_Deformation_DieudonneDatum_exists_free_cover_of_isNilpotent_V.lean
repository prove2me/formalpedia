-- Prove2me | solution 1 for Deformation.DieudonneDatum.exists_free_cover_of_isNilpotent_V
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/373eb2eb-6e71-5514-8151-bba332993777

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Theorems.Thm_Deformation_DieudonneDatum_exists_free_cover_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneDatum_exists_free_cover_of_isNilpotent_V

universe u v

namespace WEK2a

open Deformation Function

variable {A : Type u} [CommRing A] {ℓ : A}

section Helpers

variable {D : Type*} [AddCommGroup D] [Module A D]

private def _root_.WEK2a.restrict (M : DieudonneDatum ℓ D) (p : Submodule A D)
    (hF : ∀ x ∈ p, M.F x ∈ p) (hV : ∀ x ∈ p, M.V x ∈ p) : DieudonneDatum ℓ p where
  F := M.F.restrict hF
  V := M.V.restrict hV
  fv := by
    ext ⟨x, hx⟩
    simp [LinearMap.restrict_apply, M.F_V_apply]
  vf := by
    ext ⟨x, hx⟩
    simp [LinearMap.restrict_apply, M.V_F_apply]

p2m_export "WEK2a" "restrict"
variable {D₁ : Type*} [AddCommGroup D₁] [Module A D₁] {D₂ : Type*} [AddCommGroup D₂] [Module A D₂]

private def _root_.WEK2a.prod (M₁ : DieudonneDatum ℓ D₁) (M₂ : DieudonneDatum ℓ D₂) : DieudonneDatum ℓ (D₁ × D₂) where
  F := M₁.F.prodMap M₂.F
  V := M₁.V.prodMap M₂.V
  fv := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    simp [M₁.F_V_apply, M₂.F_V_apply]
  vf := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    simp [M₁.V_F_apply, M₂.V_F_apply]

p2m_export "WEK2a" "prod"

private def congr (M : DieudonneDatum ℓ D₁) (e : D₁ ≃ₗ[A] D₂) : DieudonneDatum ℓ D₂ where
  F := e.toLinearMap ∘ₗ M.F ∘ₗ e.symm.toLinearMap
  V := e.toLinearMap ∘ₗ M.V ∘ₗ e.symm.toLinearMap
  fv := by
    ext x
    simp [M.F_V_apply]
  vf := by
    ext x
    simp [M.V_F_apply]

private theorem congr_pow_apply (T : D₁ →ₗ[A] D₁) (e : D₁ ≃ₗ[A] D₂) (N : ℕ) (x : D₂) :
    ((e.toLinearMap ∘ₗ T ∘ₗ e.symm.toLinearMap) ^ N) x = e ((T ^ N) (e.symm x)) := by
  induction N generalizing x with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    simp

private theorem prodMap_pow_apply (S : D₁ →ₗ[A] D₁) (T : D₂ →ₗ[A] D₂) (N : ℕ) (x : D₁ × D₂) :
    ((S.prodMap T) ^ N) x = ((S ^ N) x.1, (T ^ N) x.2) := by
  induction N generalizing x with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, pow_succ]
    simp

private def blockEquiv {P : Type*} [AddCommGroup P] [Module A P] (G G' : P →ₗ[A] P) :
    (P × P) ≃ₗ[A] (P × P) :=
  LinearEquiv.ofLinear
    ((G ∘ₗ LinearMap.fst A P P + (LinearMap.id - G ∘ₗ G') ∘ₗ LinearMap.snd A P P).prod
      (LinearMap.fst A P P - G' ∘ₗ LinearMap.snd A P P))
    ((G' ∘ₗ LinearMap.fst A P P + (LinearMap.id - G' ∘ₗ G) ∘ₗ LinearMap.snd A P P).prod
      (LinearMap.fst A P P - G ∘ₗ LinearMap.snd A P P))
    (by
      refine LinearMap.ext fun z => Prod.ext ?_ ?_ <;> obtain ⟨x, y⟩ := z <;>
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] <;> abel)
    (by
      refine LinearMap.ext fun z => Prod.ext ?_ ?_ <;> obtain ⟨x, y⟩ := z <;>
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] <;> abel)

private theorem blockEquiv_apply {P : Type*} [AddCommGroup P] [Module A P] (G G' : P →ₗ[A] P) (x y : P) :
    blockEquiv G G' (x, y) = (G x + (y - G (G' y)), x - G' y) := rfl

private theorem blockEquiv_symm_apply {P : Type*} [AddCommGroup P] [Module A P] (G G' : P →ₗ[A] P)
    (x y : P) : (blockEquiv G G').symm (x, y) = (G' x + (y - G' (G y)), x - G y) := rfl

end Helpers

section Rfl
variable {D : Type*} [AddCommGroup D] [Module A D]
variable {D₁ : Type*} [AddCommGroup D₁] [Module A D₁] {D₂ : Type*} [AddCommGroup D₂] [Module A D₂]
@[scoped simp] private theorem restrict_F_apply (M : DieudonneDatum ℓ D) (p : Submodule A D)
    (hF : ∀ x ∈ p, M.F x ∈ p) (hV : ∀ x ∈ p, M.V x ∈ p) (x : p) :
    ((restrict M p hF hV).F x : D) = M.F x := rfl
@[scoped simp] private theorem restrict_V_apply (M : DieudonneDatum ℓ D) (p : Submodule A D)
    (hF : ∀ x ∈ p, M.F x ∈ p) (hV : ∀ x ∈ p, M.V x ∈ p) (x : p) :
    ((restrict M p hF hV).V x : D) = M.V x := rfl
private theorem restrict_F (M : DieudonneDatum ℓ D) (p : Submodule A D)
    (hF : ∀ x ∈ p, M.F x ∈ p) (hV : ∀ x ∈ p, M.V x ∈ p) : (restrict M p hF hV).F = M.F.restrict hF := rfl
private theorem restrict_V (M : DieudonneDatum ℓ D) (p : Submodule A D)
    (hF : ∀ x ∈ p, M.F x ∈ p) (hV : ∀ x ∈ p, M.V x ∈ p) : (restrict M p hF hV).V = M.V.restrict hV := rfl
@[scoped simp] private theorem prod_F_apply (M₁ : DieudonneDatum ℓ D₁) (M₂ : DieudonneDatum ℓ D₂) (x : D₁ × D₂) :
    (prod M₁ M₂).F x = (M₁.F x.1, M₂.F x.2) := rfl
@[scoped simp] private theorem prod_V_apply (M₁ : DieudonneDatum ℓ D₁) (M₂ : DieudonneDatum ℓ D₂) (x : D₁ × D₂) :
    (prod M₁ M₂).V x = (M₁.V x.1, M₂.V x.2) := rfl
private theorem prod_V (M₁ : DieudonneDatum ℓ D₁) (M₂ : DieudonneDatum ℓ D₂) :
    (prod M₁ M₂).V = M₁.V.prodMap M₂.V := rfl
@[scoped simp] private theorem congr_F_apply (M : DieudonneDatum ℓ D₁) (e : D₁ ≃ₗ[A] D₂) (x : D₂) :
    (congr M e).F x = e (M.F (e.symm x)) := rfl
@[scoped simp] private theorem congr_V_apply (M : DieudonneDatum ℓ D₁) (e : D₁ ≃ₗ[A] D₂) (x : D₂) :
    (congr M e).V x = e (M.V (e.symm x)) := rfl
private theorem congr_V (M : DieudonneDatum ℓ D₁) (e : D₁ ≃ₗ[A] D₂) :
    (congr M e).V = e.toLinearMap ∘ₗ M.V ∘ₗ e.symm.toLinearMap := rfl
end Rfl

section Etale

variable {D : Type v} [AddCommGroup D] [Module A D] [Module.Finite A D]

private theorem etale_cover (M : DieudonneDatum ℓ D) (hF : Function.Bijective M.F) :
    ∃ (s : ℕ) (M₁ : DieudonneDatum ℓ ((Fin s → A) × (Fin s → A)))
      (π : ((Fin s → A) × (Fin s → A)) →ₗ[A] D),
      Function.Surjective π ∧ π ∘ₗ M₁.F = M.F ∘ₗ π ∧ π ∘ₗ M₁.V = M.V ∘ₗ π ∧
      (∀ x, ∃ y, M₁.V x = ℓ • y) := by
  obtain ⟨s, π₀, hπ₀⟩ := Module.Finite.exists_fin' A D
  let Fe : D ≃ₗ[A] D := LinearEquiv.ofBijective M.F hF
  obtain ⟨G, hG⟩ := Module.projective_lifting_property π₀ (M.F ∘ₗ π₀) hπ₀
  obtain ⟨G', hG'⟩ := Module.projective_lifting_property π₀ (Fe.symm.toLinearMap ∘ₗ π₀) hπ₀
  have hGx : ∀ x, π₀ (G x) = M.F (π₀ x) := fun x => LinearMap.congr_fun hG x
  have hG'x : ∀ x, π₀ (G' x) = Fe.symm (π₀ x) := fun x => LinearMap.congr_fun hG' x
  have hFe : ∀ d, M.F (Fe.symm d) = d := fun d => Fe.apply_symm_apply d
  have hFe' : ∀ d, Fe.symm (M.F d) = d := fun d => Fe.symm_apply_apply d
  have hVF : ∀ d, M.V d = ℓ • Fe.symm d := fun d => by
    apply hF.1
    rw [M.F_V_apply, map_smul, hFe]
  let E := blockEquiv G G'
  refine ⟨s,
    { F := E.toLinearMap
      V := ℓ • E.symm.toLinearMap
      fv := by apply LinearMap.ext; intro x; simp
      vf := by apply LinearMap.ext; intro x; simp },
    π₀ ∘ₗ LinearMap.fst A _ _, ?_, ?_, ?_, ?_⟩
  · exact hπ₀.comp Prod.fst_surjective
  · apply LinearMap.ext
    rintro ⟨x, y⟩
    simp only [LinearMap.coe_comp, comp_apply, LinearMap.fst_apply, LinearEquiv.coe_coe]
    show π₀ (E (x, y)).1 = M.F (π₀ x)
    rw [blockEquiv_apply]
    simp only [map_add, map_sub, hGx, hG'x, hFe, sub_self, add_zero]
  · apply LinearMap.ext
    rintro ⟨x, y⟩
    simp only [LinearMap.coe_comp, comp_apply, LinearMap.fst_apply, LinearMap.smul_apply,
      LinearEquiv.coe_coe]
    show π₀ (ℓ • E.symm (x, y)).1 = M.V (π₀ x)
    rw [blockEquiv_symm_apply, hVF]
    simp only [Prod.smul_fst, map_smul, map_add, map_sub, hGx, hG'x, hFe', sub_self, add_zero]
  · intro x
    exact ⟨E.symm x, rfl⟩

end Etale

section Main

private def prodFinEquiv (a b : ℕ) : ((Fin a → A) × (Fin b → A)) ≃ₗ[A] (Fin (a + b) → A) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) A A).symm ≪≫ₗ
    LinearEquiv.funCongrLeft A A finSumFinEquiv.symm

end Main

end WEK2a
p2m_reactivate "P2MW.S_Deformation_DieudonneDatum_exists_free_cover_of_isNilpotent_V.WEK2a"

open WEK2a Deformation in
theorem solution
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ℓ : A}
    (hℓ : IsLocalRing.maximalIdeal A = Ideal.span {ℓ})
    {D : Type v} [AddCommGroup D] [Module A D] [IsNoetherian A D] [IsArtinian A D]
    (M : Deformation.DieudonneDatum ℓ D) (hV : IsNilpotent M.V) :
    ∃ (r N : ℕ) (M₁ : Deformation.DieudonneDatum ℓ (Fin r → A)) (π : (Fin r → A) →ₗ[A] D),
      Function.Surjective π ∧ π ∘ₗ M₁.F = M.F ∘ₗ π ∧ π ∘ₗ M₁.V = M.V ∘ₗ π ∧
      (∀ x, ∃ y, (M₁.V ^ N) x = ℓ • y) ∧ Function.Injective M₁.V := by
  classical
  have hℓ0 : ℓ ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field A
    rw [hℓ, h, Ideal.span_singleton_eq_bot]

  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    (M.F.eventually_isCompl_ker_pow_range_pow.and
      (M.F.eventually_iInf_range_pow_eq.and M.F.eventually_iSup_ker_pow_eq))
  obtain ⟨hcompl, hrange, hker⟩ := hn n le_rfl
  obtain ⟨-, hrange1, hker1⟩ := hn (n + 1) (Nat.le_succ n)
  have hkk : LinearMap.ker (M.F ^ (n + 1)) = LinearMap.ker (M.F ^ n) := by rw [← hker1, hker]
  have hrr : LinearMap.range (M.F ^ (n + 1)) = LinearMap.range (M.F ^ n) := by
    rw [← hrange1, hrange]
  set p : Submodule A D := LinearMap.ker (M.F ^ n) with hp
  set q : Submodule A D := LinearMap.range (M.F ^ n) with hq
  have hcomm : ∀ (m : ℕ) (x : D), (M.F ^ m) (M.V x) = M.V ((M.F ^ m) x) := fun m x =>
    LinearMap.congr_fun ((Commute.symm (show Commute M.V M.F from M.F_V_comm.symm)).pow_left m).eq x
  have hpF : ∀ x ∈ p, M.F x ∈ p := fun x hx => by
    have hx' : (M.F ^ n) x = 0 := hx
    show (M.F ^ n) (M.F x) = 0
    rw [← Module.End.mul_apply, ← pow_succ, ← LinearMap.mem_ker, hkk, LinearMap.mem_ker, hx']
  have hpV : ∀ x ∈ p, M.V x ∈ p := fun x hx => by
    have hx' : (M.F ^ n) x = 0 := hx
    show (M.F ^ n) (M.V x) = 0
    rw [hcomm, hx', map_zero]
  have hqF : ∀ x ∈ q, M.F x ∈ q := by
    rintro _ ⟨y, rfl⟩
    refine ⟨M.F y, ?_⟩
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]
  have hqV : ∀ x ∈ q, M.V x ∈ q := by
    rintro _ ⟨y, rfl⟩
    exact ⟨M.V y, hcomm n y⟩

  let Mp := restrict M p hpF hpV
  let Mq := restrict M q hqF hqV
  have hFnil : IsNilpotent Mp.F := by
    refine ⟨n, ?_⟩
    rw [restrict_F, Module.End.pow_restrict]
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    exact Subtype.ext hx
  have hVnil : IsNilpotent Mp.V := by
    obtain ⟨m, hm⟩ := hV
    refine ⟨m, ?_⟩
    rw [restrict_V, Module.End.pow_restrict]
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    refine Subtype.ext ?_
    simp [LinearMap.restrict_apply, hm]
  have hbij : Function.Bijective Mq.F := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨_, y, rfl⟩ hy
      have hy' : M.F ((M.F ^ n) y) = 0 := congrArg Subtype.val hy
      have hmem : y ∈ LinearMap.ker (M.F ^ (n + 1)) := by
        rw [LinearMap.mem_ker, pow_succ', Module.End.mul_apply, hy']
      rw [hkk, LinearMap.mem_ker] at hmem
      exact Subtype.ext hmem
    · rintro ⟨x, hx⟩
      have hx' : x ∈ LinearMap.range (M.F ^ (n + 1)) := by rw [hrr]; exact hx
      obtain ⟨z, rfl⟩ := hx'
      refine ⟨⟨(M.F ^ n) z, ⟨z, rfl⟩⟩, Subtype.ext ?_⟩
      show M.F ((M.F ^ n) z) = (M.F ^ (n + 1)) z
      rw [pow_succ', Module.End.mul_apply]

  obtain ⟨r₁, N₁, k, Mn, πn, hπn, hπnF, hπnV, hk, -, hVN⟩ :=
    Deformation.DieudonneDatum.exists_free_cover_of_isNilpotent Mp hFnil hVnil
  obtain ⟨s, Me, πe, hπe, hπeF, hπeV, hVe⟩ := etale_cover Mq hbij

  let P := (Fin r₁ → A) × ((Fin s → A) × (Fin s → A))
  let Ms : DieudonneDatum ℓ P := prod Mn Me
  let πs : P →ₗ[A] D :=
    p.subtype ∘ₗ πn ∘ₗ LinearMap.fst A _ _ + q.subtype ∘ₗ πe ∘ₗ LinearMap.snd A _ _
  let e : P ≃ₗ[A] (Fin (r₁ + (s + s)) → A) :=
    (LinearEquiv.refl A (Fin r₁ → A)).prodCongr (prodFinEquiv s s) ≪≫ₗ prodFinEquiv r₁ (s + s)
  have hπsF : ∀ z : P, πs (Ms.F z) = M.F (πs z) := fun z => by
    obtain ⟨z₁, z₂⟩ := z
    show (πn (Mn.F z₁) : D) + (πe (Me.F z₂) : D) = M.F ((πn z₁ : D) + (πe z₂ : D))
    rw [map_add, show πn (Mn.F z₁) = Mp.F (πn z₁) from LinearMap.congr_fun hπnF z₁,
      show πe (Me.F z₂) = Mq.F (πe z₂) from LinearMap.congr_fun hπeF z₂]
    rfl
  have hπsV : ∀ z : P, πs (Ms.V z) = M.V (πs z) := fun z => by
    obtain ⟨z₁, z₂⟩ := z
    show (πn (Mn.V z₁) : D) + (πe (Me.V z₂) : D) = M.V ((πn z₁ : D) + (πe z₂ : D))
    rw [map_add, show πn (Mn.V z₁) = Mp.V (πn z₁) from LinearMap.congr_fun hπnV z₁,
      show πe (Me.V z₂) = Mq.V (πe z₂) from LinearMap.congr_fun hπeV z₂]
    rfl
  refine ⟨r₁ + (s + s), N₁ + 1, congr Ms e, πs ∘ₗ e.symm.toLinearMap, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro d
    have hd : d ∈ p ⊔ q := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hd
    obtain ⟨a, ha⟩ := hπn ⟨y, hy⟩
    obtain ⟨b, hb⟩ := hπe ⟨z, hz⟩
    refine ⟨e (a, b), ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    show (πn a : D) + (πe b : D) = y + z
    rw [ha, hb]
  · apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, congr_F_apply,
      LinearEquiv.symm_apply_apply, hπsF]
  · apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, congr_V_apply,
      LinearEquiv.symm_apply_apply, hπsV]
  ·
    intro x
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨yb, hyb⟩ := hVe ((Me.V ^ N₁) (e.symm x).2)
    refine ⟨e (ℓ ^ k' • Mn.V (e.symm x).1, yb), ?_⟩
    rw [congr_V, congr_pow_apply, prod_V, prodMap_pow_apply, ← map_smul]
    congr 1
    refine Prod.ext ?_ ?_
    · show (Mn.V ^ (N₁ + 1)) (e.symm x).1 = (ℓ • (ℓ ^ k' • Mn.V (e.symm x).1, yb)).1
      rw [Prod.smul_fst, pow_succ', Module.End.mul_apply, LinearMap.congr_fun hVN (e.symm x).1]
      simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, smul_smul, pow_succ']
    · show (Me.V ^ (N₁ + 1)) (e.symm x).2 = (ℓ • (ℓ ^ k' • Mn.V (e.symm x).1, yb)).2
      rw [Prod.smul_snd, pow_succ', Module.End.mul_apply, hyb]
  ·
    intro x y hxy
    have h := congrArg (congr Ms e).F hxy
    rw [(congr Ms e).F_V_apply, (congr Ms e).F_V_apply] at h
    exact smul_right_injective _ hℓ0 h

end S_Deformation_DieudonneDatum_exists_free_cover_of_isNilpotent_V
end P2MW
export P2MW.S_Deformation_DieudonneDatum_exists_free_cover_of_isNilpotent_V (solution)
