-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6cb96618-339b-53c6-aa99-5abba9d34dc5

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isBaseChangeAlong_of_isLocalization
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_map_of_isBaseChangeAlong
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_pullback_of_isTranslateEven
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_pullback_of_isTranslateOdd
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateEven_or_exists_isTranslateOdd
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_exists_mul_eq_and_map_eq_of_isBaseChange_of_inEdgeChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace ReduceTLCC

theorem surjective_loc {R T R₁ T₁ : Type} [CommRing R] [CommRing T] [CommRing R₁] [CommRing T₁]
    [Algebra R R₁] [Algebra T T₁] (φ : R →+* T) (r : R)
    [IsLocalization.Away r R₁] [IsLocalization.Away (φ r) T₁]
    (φ₁ : R₁ →+* T₁) (h : φ₁.comp (algebraMap R R₁) = (algebraMap T T₁).comp φ)
    (hφ : Function.Surjective φ) : Function.Surjective φ₁ := by
  intro y
  obtain ⟨n, a, hy⟩ := IsLocalization.Away.surj (φ r) y
  obtain ⟨b, rfl⟩ := hφ a
  have hu : IsUnit (algebraMap R R₁ r) := IsLocalization.Away.algebraMap_isUnit r
  obtain ⟨u, hu'⟩ := hu
  have hφu : φ₁ (u : R₁) = algebraMap T T₁ (φ r) := by
    rw [hu']; exact RingHom.congr_fun h r
  refine ⟨algebraMap R R₁ b * ((u⁻¹ : R₁ˣ) : R₁) ^ n, ?_⟩
  have hunit : IsUnit (algebraMap T T₁ (φ r) ^ n) := (IsLocalization.Away.algebraMap_isUnit (φ r)).pow n
  rw [← hunit.mul_left_inj, hy, map_mul, map_pow, mul_assoc, ← mul_pow, ← hφu, ← map_mul,
    Units.inv_mul, map_one, one_pow, mul_one]
  exact RingHom.congr_fun h b

theorem ker_loc_le {R T R₁ T₁ : Type} [CommRing R] [CommRing T] [CommRing R₁] [CommRing T₁]
    [Algebra R R₁] [Algebra T T₁] (φ : R →+* T) (r : R)
    [IsLocalization.Away r R₁] [IsLocalization.Away (φ r) T₁]
    (φ₁ : R₁ →+* T₁) (h : φ₁.comp (algebraMap R R₁) = (algebraMap T T₁).comp φ) :
    RingHom.ker φ₁ ≤ Ideal.map (algebraMap R R₁) (RingHom.ker φ) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  obtain ⟨n, a, hxa⟩ := IsLocalization.Away.surj r x
  have h0 : algebraMap T T₁ (φ a) = algebraMap T T₁ 0 := by
    rw [map_zero, ← RingHom.comp_apply, ← h, RingHom.comp_apply, ← hxa, map_mul, hx, zero_mul]
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (S := T₁) (φ r) h0
  rw [mul_zero, ← map_pow, ← map_mul, ← RingHom.mem_ker] at hm
  have hmem : algebraMap R R₁ (r ^ m * a) ∈ Ideal.map (algebraMap R R₁) (RingHom.ker φ) :=
    Ideal.mem_map_of_mem _ hm
  have hu : IsUnit (algebraMap R R₁ r ^ (m + n)) := (IsLocalization.Away.algebraMap_isUnit r).pow _
  obtain ⟨u, hu'⟩ := hu
  have hx' : x = algebraMap R R₁ (r ^ m * a) * ((u⁻¹ : R₁ˣ) : R₁) := by
    rw [map_mul, map_pow, ← hxa, eq_comm, Units.mul_inv_eq_iff_eq_mul, hu', pow_add]; ring
  rw [hx']
  exact Ideal.mul_mem_right _ _ hmem

theorem isNilpotent_ker_loc {R T R₁ T₁ : Type} [CommRing R] [CommRing T] [CommRing R₁] [CommRing T₁]
    [Algebra R R₁] [Algebra T T₁] (φ : R →+* T) (r : R)
    [IsLocalization.Away r R₁] [IsLocalization.Away (φ r) T₁]
    (φ₁ : R₁ →+* T₁) (h : φ₁.comp (algebraMap R R₁) = (algebraMap T T₁).comp φ)
    (hn : IsNilpotent (RingHom.ker φ)) : IsNilpotent (RingHom.ker φ₁) := by
  obtain ⟨N, hN⟩ := hn
  refine ⟨N, ?_⟩
  rw [Submodule.zero_eq_bot] at hN ⊢
  have h1 : RingHom.ker φ₁ ^ N ≤ Ideal.map (algebraMap R R₁) (RingHom.ker φ ^ N) := by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono (ker_loc_le φ r φ₁ h) N
  rw [hN, Ideal.map_bot] at h1
  exact le_bot_iff.mp h1

theorem exists_cover_of_forall_maximal {R : Type} [CommRing R] (P : R → Prop)
    (h : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → ∃ r, r ∉ 𝔪 ∧ P r) :
    ∃ (n : ℕ) (f : Fin n → R), Ideal.span (Set.range f) = ⊤ ∧ ∀ i, P (f i) := by
  classical
  have htop : Ideal.span {r : R | P r} = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hPr⟩ := h 𝔪 h𝔪
    exact hr (hle (Ideal.subset_span hPr))
  have h1 : (1 : R) ∈ Ideal.span {r : R | P r} := by rw [htop]; trivial
  obtain ⟨T, hTS, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨T.card, fun i => (T.equivFin.symm i : R), ?_, fun i => hTS (T.equivFin.symm i).2⟩
  have hrange : Set.range (fun i : Fin T.card => ((T.equivFin.symm i) : R)) = (T : Set R) := by
    ext r; constructor
    · rintro ⟨i, rfl⟩; exact (T.equivFin.symm i).2
    · intro hr; exact ⟨T.equivFin ⟨r, hr⟩, by simp⟩
  rw [hrange, Ideal.eq_top_iff_one]
  exact h1T

theorem ker_le_of_isPrime {R T : Type} [CommRing R] [CommRing T] (φ : R →+* T)
    (hn : IsNilpotent (RingHom.ker φ)) (𝔭 : Ideal R) (h𝔭 : 𝔭.IsPrime) : RingHom.ker φ ≤ 𝔭 := by
  obtain ⟨N, hN⟩ := hn
  intro y hy
  have : y ^ N ∈ RingHom.ker φ ^ N := Ideal.pow_mem_pow hy N
  rw [hN] at this
  exact h𝔭.mem_of_pow_mem N (by rw [Ideal.mem_bot.mp this]; exact 𝔭.zero_mem)

theorem isMaximal_map_of_surjective {R T : Type} [CommRing R] [CommRing T] (φ : R →+* T)
    (hφ : Function.Surjective φ) (hn : IsNilpotent (RingHom.ker φ))
    (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal) : (Ideal.map φ 𝔪).IsMaximal := by
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective φ hφ h𝔪 with h | h
  · exfalso
    have hc := Ideal.comap_map_of_surjective φ hφ 𝔪
    rw [h, Ideal.comap_top] at hc
    have hk : Ideal.comap φ ⊥ ≤ 𝔪 := by
      rw [← RingHom.ker_eq_comap_bot]; exact ker_le_of_isPrime φ hn 𝔪 h𝔪.isPrime
    exact h𝔪.ne_top (top_le_iff.mp (hc.le.trans (sup_le le_rfl hk)))
  · exact h

theorem not_mem_of_apply_not_mem_map {R T : Type} [CommRing R] [CommRing T] (φ : R →+* T)
    (𝔪 : Ideal R) (a : R) (h : φ a ∉ Ideal.map φ 𝔪) : a ∉ 𝔪 :=
  fun ha => h (Ideal.mem_map_of_mem φ ha)

theorem isBaseChange_iff_eq_map {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (d : DeligneDatum (K := K) π B) (d' : DeligneDatum (K := K) π B') :
    DeligneDatum.IsBaseChange (K := K) (π := π) f d d' ↔ d' = d.map π f :=
  ⟨fun h => DeligneDatum.ext' (funext fun M => (h M).trans ((DeligneDatum.isBaseChange_map π f d) M).symm),
   fun h => h ▸ DeligneDatum.isBaseChange_map π f d⟩

theorem dmap_comp {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B₁ B₂ B₃ : Type} [CommRing B₁] [Algebra 𝒪 B₁] [CommRing B₂] [Algebra 𝒪 B₂] [CommRing B₃] [Algebra 𝒪 B₃]
    (f : B₁ →ₐ[𝒪] B₂) (g : B₂ →ₐ[𝒪] B₃) (d : DeligneDatum (K := K) π B₁) :
    d.map π (g.comp f) = (d.map π f).map π g :=
  (Omega K π).map_comp f g d

def algHomOf {R S S' : Type} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    (g : S →+* S') (hg : ∀ z : R, g (algebraMap R S z) = algebraMap R S' z) : S →ₐ[R] S' :=
  { toRingHom := g, commutes' := hg }

@[scoped simp] theorem coe_algHomOf {R S S' : Type} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    (g : S →+* S') (hg : ∀ z : R, g (algebraMap R S z) = algebraMap R S' z) :
    (algHomOf g hg : S →+* S') = g := RingHom.ext fun _ => rfl

theorem existsUnique_of_forall_exists_smul {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Invertible R M] (e : M) (h : ∀ t : M, ∃ b : R, t = b • e) : ∀ t : M, ∃! b : R, t = b • e := by
  intro t
  obtain ⟨b, hb⟩ := h t
  refine ⟨b, hb, fun b' hb' => ?_⟩
  refine FaithfulSMul.eq_of_smul_eq_smul (α := M) (fun m => ?_)
  obtain ⟨c, rfl⟩ := h m
  rw [smul_comm b' c e, smul_comm b c e, ← hb', ← hb]

end ReduceTLCC
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange.ReduceTLCC"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) [Finite (𝒪 ⧸ Ideal.span {π})]
    {B B' : Type} [CommRing B] [CommRing B'] [Algebra 𝒪 B] [Algebra 𝒪 B']
    (φ : B' →ₐ[𝒪] B) (hφs : Function.Surjective φ) (hφn : IsNilpotent (RingHom.ker (φ : B' →+* B)))
    (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    {Q : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B} (hQ : Q.IsQuadrupleOf d)
    (e₀ : Q.T₀) (e₁ : Q.T₁)
    (he₀ : ∀ t : Q.T₀, ∃! b : B, t = b • e₀) (he₁ : ∀ t : Q.T₁, ∃! b : B, t = b • e₁)
    (α β : B) (hα : Q.Pi₀ e₀ = α • e₁) (hβ : Q.Pi₁ e₁ = β • e₀)
    (d' : DeligneDatum (K := K) π B')
    (hd' : DeligneDatum.IsBaseChange (K := K) (π := π) φ d' d) :
    ∃ (n : ℕ) (f : Fin n → B'), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L' : Type) [CommRing L'] [Algebra B' L'] [IsLocalization.Away (f i) L']
        (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (φ (f i)) L]
        (φL : L' →+* L) (_hφL : φL.comp (algebraMap B' L') = (algebraMap B L).comp (φ : B' →+* B)),
        ∃ α' β' : L', φL α' = algebraMap B L α ∧ φL β' = algebraMap B L β ∧
          α' * β' = algebraMap B' L' (algebraMap 𝒪 B' π) := by
  classical

  let P : B' → Prop := fun r' =>
    ∀ (L' : Type) [CommRing L'] [Algebra B' L'] [IsLocalization.Away r' L']
      (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (φ r') L]
      (φL : L' →+* L) (_hφL : φL.comp (algebraMap B' L') = (algebraMap B L).comp (φ : B' →+* B)),
      ∃ α' β' : L', φL α' = algebraMap B L α ∧ φL β' = algebraMap B L β ∧
        α' * β' = algebraMap B' L' (algebraMap 𝒪 B' π)
  suffices hpt : ∀ 𝔪 : Ideal B', 𝔪.IsMaximal → ∃ r, r ∉ 𝔪 ∧ P r by
    obtain ⟨n, f, hf, hP⟩ := ReduceTLCC.exists_cover_of_forall_maximal P hpt
    exact ⟨n, f, hf, fun i => hP i⟩
  intro 𝔪 h𝔪
  have hB : IsNilpotent (algebraMap 𝒪 B π) := by
    obtain ⟨m, hm⟩ := hB'
    exact ⟨m, by rw [← φ.commutes, ← map_pow, hm, map_zero]⟩

  have hπK : algebraMap 𝒪 K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).mpr hπ.ne_zero
  let g : Matrix.GeneralLinearGroup (Fin 2) K := diagFst K (Units.mk0 _ hπK)
  have hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1] := diagFst_coe K _

  obtain ⟨s, hs, hcov⟩ :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq π hπ
      (Nat.card (𝒪 ⧸ Ideal.span {π})) rfl g hg hB d
  set 𝔭 : Ideal B := Ideal.map (φ : B' →+* B) 𝔪 with h𝔭def
  have h𝔭 : 𝔭.IsMaximal := ReduceTLCC.isMaximal_map_of_surjective (φ : B' →+* B) hφs hφn 𝔪 h𝔪
  obtain ⟨r, hrs, hr⟩ : ∃ r ∈ s, r ∉ 𝔭 := by
    by_contra hall
    push_neg at hall
    have : Ideal.span (s : Set B) ≤ 𝔭 := Ideal.span_le.mpr (fun r hr => hall r hr)
    rw [hs, top_le_iff] at this
    exact h𝔭.ne_top this
  obtain ⟨h, x, hIn, hx0, hx1⟩ := hcov r hrs
  let Lr : Type := Localization.Away r
  let toB : B →ₐ[𝒪] Lr := IsScalarTower.toAlgHom 𝒪 B Lr
  let dL : DeligneDatum (K := K) π Lr := d.map π toB

  obtain ⟨QL, hbc⟩ := CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isBaseChangeAlong_of_isLocalization Q (Submonoid.powers r) Lr
  obtain ⟨W⟩ := hbc
  have hQL : QL.IsQuadrupleOf dL :=
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.map_of_isBaseChangeAlong toB hQ ⟨W⟩
  let eL₀ : QL.T₀ := W.τ₀ e₀
  let eL₁ : QL.T₁ := W.τ₁ e₁
  have htoB : ∀ b : B, (toB : B →+* Lr) b = algebraMap B Lr b := fun b => rfl
  have hgen₀ : ∀ t : QL.T₀, ∃ b : Lr, t = b • eL₀ := by
    intro t
    have ht : t ∈ Submodule.span Lr (Set.range W.τ₀) := by rw [W.span_range_τ₀]; trivial
    have hle : Submodule.span Lr (Set.range W.τ₀) ≤ Submodule.span Lr {eL₀} := by
      apply Submodule.span_le.mpr
      rintro _ ⟨s0, rfl⟩
      obtain ⟨b, hb, -⟩ := he₀ s0
      rw [hb, LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hle ht)
    exact ⟨b, hb.symm⟩
  have hgen₁ : ∀ t : QL.T₁, ∃ b : Lr, t = b • eL₁ := by
    intro t
    have ht : t ∈ Submodule.span Lr (Set.range W.τ₁) := by rw [W.span_range_τ₁]; trivial
    have hle : Submodule.span Lr (Set.range W.τ₁) ≤ Submodule.span Lr {eL₁} := by
      apply Submodule.span_le.mpr
      rintro _ ⟨s0, rfl⟩
      obtain ⟨b, hb, -⟩ := he₁ s0
      rw [hb, LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hle ht)
    exact ⟨b, hb.symm⟩
  have heL₀ : ∀ t : QL.T₀, ∃! b : Lr, t = b • eL₀ := ReduceTLCC.existsUnique_of_forall_exists_smul eL₀ hgen₀
  have heL₁ : ∀ t : QL.T₁, ∃! b : Lr, t = b • eL₁ := ReduceTLCC.existsUnique_of_forall_exists_smul eL₁ hgen₁
  have hαL : QL.Pi₀ eL₀ = algebraMap B Lr α • eL₁ := by
    show QL.Pi₀ (W.τ₀ e₀) = algebraMap B Lr α • W.τ₁ e₁
    rw [← W.τ₁_Pi₀, hα, LinearMap.map_smulₛₗ]; rfl
  have hβL : QL.Pi₁ eL₁ = algebraMap B Lr β • eL₀ := by
    show QL.Pi₁ (W.τ₁ e₁) = algebraMap B Lr β • W.τ₀ e₀
    rw [← W.τ₀_Pi₁, hβ, LinearMap.map_smulₛₗ]; rfl

  obtain ⟨r', hr'⟩ := hφs r
  have hr'e : (φ : B' →+* B) r' = r := hr'
  have hr'𝔪 : r' ∉ 𝔪 := ReduceTLCC.not_mem_of_apply_not_mem_map (φ : B' →+* B) 𝔪 r' (by rw [hr'e]; exact hr)
  let L'r : Type := Localization.Away r'
  let toB' : B' →ₐ[𝒪] L'r := IsScalarTower.toAlgHom 𝒪 B' L'r
  have hu : IsUnit (((algebraMap B Lr).comp (φ : B' →+* B)) r') := by
    rw [RingHom.comp_apply, hr'e]; exact IsLocalization.Away.algebraMap_isUnit r
  let φr : L'r →+* Lr := IsLocalization.Away.lift r' (g := (algebraMap B Lr).comp (φ : B' →+* B)) hu
  have hφr : φr.comp (algebraMap B' L'r) = (algebraMap B Lr).comp (φ : B' →+* B) := IsLocalization.Away.lift_comp _ _
  have hφra : ∀ b : B', φr (algebraMap B' L'r b) = algebraMap B Lr ((φ : B' →+* B) b) := fun b => RingHom.congr_fun hφr b
  haveI : IsLocalization.Away ((φ : B' →+* B) r') Lr := by rw [hr'e]; infer_instance
  have hφrs : Function.Surjective φr := ReduceTLCC.surjective_loc (φ : B' →+* B) r' φr hφr hφs
  have hφrn : IsNilpotent (RingHom.ker φr) := ReduceTLCC.isNilpotent_ker_loc (φ : B' →+* B) r' φr hφr hφn
  let φrₐ : L'r →ₐ[𝒪] Lr := ReduceTLCC.algHomOf φr (fun z => by
    rw [IsScalarTower.algebraMap_apply 𝒪 B' L'r z, hφra, IsScalarTower.algebraMap_apply 𝒪 B Lr]
    exact congrArg (algebraMap B Lr) (φ.commutes z))
  have hφrₐs : Function.Surjective φrₐ := hφrs
  have hφrₐn : IsNilpotent (RingHom.ker (φrₐ : L'r →+* Lr)) := by rw [ReduceTLCC.coe_algHomOf]; exact hφrn
  have hL'r : IsNilpotent (algebraMap 𝒪 L'r π) := by
    obtain ⟨m, hm⟩ := hB'
    exact ⟨m, by rw [IsScalarTower.algebraMap_apply 𝒪 B' L'r, ← map_pow, hm, map_zero]⟩
  let d'r : DeligneDatum (K := K) π L'r := d'.map π toB'
  have hd'r : DeligneDatum.IsBaseChange (K := K) (π := π) φrₐ d'r dL := by
    rw [ReduceTLCC.isBaseChange_iff_eq_map]
    have e3 : d = d'.map π φ := (ReduceTLCC.isBaseChange_iff_eq_map _ _ _).mp hd'
    have e4 : toB.comp φ = φrₐ.comp toB' := by
      apply AlgHom.ext; intro b
      show algebraMap B Lr (φ b) = φr (algebraMap B' L'r b)
      exact (hφra b).symm
    show d.map π toB = (d'.map π toB').map π φrₐ
    rw [e3, ← ReduceTLCC.dmap_comp, ← ReduceTLCC.dmap_comp, e4]
  let dLh : DeligneDatum (K := K) π Lr := DeligneDatum.pullback π Lr h dL
  let d'rh : DeligneDatum (K := K) π L'r := DeligneDatum.pullback π L'r h d'r
  have hbch : DeligneDatum.IsBaseChange (K := K) (π := π) φrₐ d'rh dLh := by
    rw [ReduceTLCC.isBaseChange_iff_eq_map, DeligneDatum.map_pullback,
      ← (ReduceTLCC.isBaseChange_iff_eq_map _ _ _).mp hd'r]
  have transfer : ∀ {M₁ N₁ : Type} [AddCommGroup M₁] [AddCommGroup N₁] [Module Lr M₁] [Module Lr N₁]
      (τ : M₁ ≃ₗ[Lr] N₁) (e : M₁), (∀ t : M₁, ∃! b : Lr, t = b • e) → ∀ t : N₁, ∃! b : Lr, t = b • τ e := by
    intro M₁ N₁ _ _ _ _ τ e hh t
    obtain ⟨b, hb, huniq⟩ := hh (τ.symm t)
    refine ⟨b, ?_, fun b' hb' => huniq b' ?_⟩
    · show t = b • τ e
      rw [← map_smul, ← hb, LinearEquiv.apply_symm_apply]
    · show τ.symm t = b' • e
      have hb'' : t = b' • τ e := hb'
      rw [hb'', map_smul, LinearEquiv.symm_apply_apply]

  have core : ∃ a' b' : L'r, φr a' = algebraMap B Lr α ∧ φr b' = algebraMap B Lr β ∧ a' * b' = algebraMap 𝒪 L'r π := by
    rcases CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateEven_or_exists_isTranslateOdd hπ QL h with
      ⟨c, Qh, ⟨Wt⟩⟩ | ⟨c₀, c₁, Qh, ⟨Wo⟩⟩
    · have hQh : Qh.IsQuadrupleOf dLh :=
        CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.pullback_of_isTranslateEven h c hQL ⟨Wt⟩
      have hf₀ : ∀ t : Qh.T₀, ∃! b : Lr, t = b • Wt.τ₀ eL₀ := by
        exact transfer Wt.τ₀ eL₀ heL₀
      have hf₁ : ∀ t : Qh.T₁, ∃! b : Lr, t = b • Wt.τ₁ eL₁ := by
        exact transfer Wt.τ₁ eL₁ heL₁
      have hpa : Qh.Pi₀ (Wt.τ₀ eL₀) = algebraMap B Lr α • Wt.τ₁ eL₁ := by rw [← Wt.τ₁_Pi₀, hαL, map_smul]
      have hpb : Qh.Pi₁ (Wt.τ₁ eL₁) = algebraMap B Lr β • Wt.τ₀ eL₀ := by rw [← Wt.τ₀_Pi₁, hβL, map_smul]
      obtain ⟨a', b', ha', hb', hab'⟩ :=
        CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.exists_mul_eq_and_map_eq_of_isBaseChange_of_inEdgeChart π hπ
          (Nat.card (𝒪 ⧸ Ideal.span {π})) rfl g hg φrₐ hφrₐs hφrₐn hL'r dLh hIn x hx0 hx1 Qh hQh
          (Wt.τ₀ eL₀) (Wt.τ₁ eL₁) hf₀ hf₁ (algebraMap B Lr α) (algebraMap B Lr β) hpa hpb d'rh hbch
      exact ⟨a', b', ha', hb', hab'⟩
    · have hQh : Qh.IsQuadrupleOf dLh :=
        CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.pullback_of_isTranslateOdd h c₀ c₁ hQL ⟨Wo⟩
      have hf₀ : ∀ t : Qh.T₀, ∃! b : Lr, t = b • Wo.σ₀ eL₁ := by
        exact transfer Wo.σ₀ eL₁ heL₁
      have hf₁ : ∀ t : Qh.T₁, ∃! b : Lr, t = b • Wo.σ₁ eL₀ := by
        exact transfer Wo.σ₁ eL₀ heL₀
      have hpa : Qh.Pi₀ (Wo.σ₀ eL₁) = algebraMap B Lr β • Wo.σ₁ eL₀ := by rw [← Wo.σ₁_Pi₁, hβL, map_smul]
      have hpb : Qh.Pi₁ (Wo.σ₁ eL₀) = algebraMap B Lr α • Wo.σ₀ eL₁ := by rw [← Wo.σ₀_Pi₀, hαL, map_smul]
      obtain ⟨a', b', ha', hb', hab'⟩ :=
        CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.exists_mul_eq_and_map_eq_of_isBaseChange_of_inEdgeChart π hπ
          (Nat.card (𝒪 ⧸ Ideal.span {π})) rfl g hg φrₐ hφrₐs hφrₐn hL'r dLh hIn x hx0 hx1 Qh hQh
          (Wo.σ₀ eL₁) (Wo.σ₁ eL₀) hf₀ hf₁ (algebraMap B Lr β) (algebraMap B Lr α) hpa hpb d'rh hbch
      exact ⟨b', a', hb', ha', by rw [mul_comm]; exact hab'⟩
  obtain ⟨a', b', ha', hb', hab'⟩ := core

  refine ⟨r', hr'𝔪, ?_⟩
  intro L' _ _ _ L _ _ _ φL hφL
  let e' : L'r →+* L' := IsLocalization.Away.lift r' (g := algebraMap B' L') (IsLocalization.Away.algebraMap_isUnit r')
  have he' : e'.comp (algebraMap B' L'r) = algebraMap B' L' := IsLocalization.Away.lift_comp _ _
  haveI instL : IsLocalization.Away ((φ : B' →+* B) r') L := ‹IsLocalization.Away (φ r') L›
  have hur : IsUnit (algebraMap B L r) := by rw [← hr'e]; exact IsLocalization.Away.algebraMap_isUnit ((φ : B' →+* B) r')
  let e : Lr →+* L := IsLocalization.Away.lift r (g := algebraMap B L) hur
  have he : e.comp (algebraMap B Lr) = algebraMap B L := IsLocalization.Away.lift_comp _ _
  have hcomm : φL.comp e' = e.comp φr := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r')
    rw [RingHom.comp_assoc, he', hφL, RingHom.comp_assoc, hφr, ← RingHom.comp_assoc, he]
  refine ⟨e' a', e' b', ?_, ?_, ?_⟩
  · have := RingHom.congr_fun hcomm a'
    rw [RingHom.comp_apply, RingHom.comp_apply, ha'] at this
    rw [this]; exact RingHom.congr_fun he α
  · have := RingHom.congr_fun hcomm b'
    rw [RingHom.comp_apply, RingHom.comp_apply, hb'] at this
    rw [this]; exact RingHom.congr_fun he β
  · rw [← map_mul, hab', IsScalarTower.algebraMap_apply 𝒪 B' L'r π]
    exact RingHom.congr_fun he' _

#print axioms solution

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange (solution)
