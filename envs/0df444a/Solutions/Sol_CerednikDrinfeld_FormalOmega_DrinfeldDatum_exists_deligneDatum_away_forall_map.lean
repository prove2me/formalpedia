-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_deligneDatum_away_forall_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9c127bda-1dcf-5079-8701-730211019bc7

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isOpen_forall_lattice_eq_or_bijective_map
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_compatible_linearMap_pair_mk_tmul_eq_smul
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_inEdgeChart_and_line_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_localDeligneDatum
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_deligneDatum_away_forall_map

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega TensorProduct

noncomputable section

namespace P2mKcQuadrupleLocalModel

section Loc

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

abbrev toAway (r : B) : B →ₐ[𝒪] Localization.Away r :=
  IsScalarTower.toAlgHom 𝒪 B (Localization.Away r)

abbrev awayMap (r : B) (M : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K (Localization.Away r) M :=
  AlgebraTensorModule.rTensor 𝒪 (↥M.1) (Algebra.linearMap B (Localization.Away r))

scoped instance awayMap_isLocalizedModule (r : B) (M : FullLattice 𝒪 K) :
    IsLocalizedModule (Submonoid.powers r) (awayMap (𝒪 := 𝒪) (K := K) r M) := by
  infer_instance

theorem awayMap_apply (r : B) (M : FullLattice 𝒪 K) (y : latticeBaseChange 𝒪 K B M) :
    awayMap r M y = LinearMap.rTensor (↥M.1) (toAway (𝒪 := 𝒪) r).toLinearMap y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b v => rfl

abbrev locMap (x : PrimeSpectrum B) (M : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K (locRing B x) M :=
  AlgebraTensorModule.rTensor 𝒪 (↥M.1) (Algebra.linearMap B (locRing B x))

scoped instance locMap_isLocalizedModule (x : PrimeSpectrum B) (M : FullLattice 𝒪 K) :
    IsLocalizedModule x.asIdeal.primeCompl (locMap (𝒪 := 𝒪) (K := K) x M) := by
  infer_instance

theorem locMap_apply (x : PrimeSpectrum B) (M : FullLattice 𝒪 K) (y : latticeBaseChange 𝒪 K B M) :
    locMap x M y = LinearMap.rTensor (↥M.1) (toLocRing B x).toLinearMap y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b v => rfl

theorem locMap_one_tmul (x : PrimeSpectrum B) (M : FullLattice 𝒪 K) (v : ↥M.1) :
    locMap x M ((1 : B) ⊗ₜ[𝒪] v) = (1 : locRing B x) ⊗ₜ[𝒪] v := by
  rw [locMap_apply, rTensor_one_tmul]

abbrev awaySub (r : B) (M : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B M)) :
    Submodule (Localization.Away r) (latticeBaseChange 𝒪 K (Localization.Away r) M) :=
  N.localized' (Localization.Away r) (Submonoid.powers r) (awayMap r M)

def awayToLoc (r : B) (y : PrimeSpectrum B) (hr : r ∉ y.asIdeal) : Localization.Away r →ₐ[𝒪] locRing B y :=
  IsLocalization.liftAlgHom (M := Submonoid.powers r) (f := toLocRing B y) fun s => by
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have hs : (s : B) ∉ y.asIdeal := by
      rw [← hn]
      exact fun h => hr (y.2.mem_of_pow_mem n h)
    exact IsLocalization.map_units (locRing B y) (⟨s, hs⟩ : y.asIdeal.primeCompl)

theorem awayToLoc_algebraMap (r : B) (y : PrimeSpectrum B) (hr : r ∉ y.asIdeal) (b : B) :
    awayToLoc (𝒪 := 𝒪) r y hr (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B y) b := by
  rw [awayToLoc, IsLocalization.liftAlgHom_apply]
  exact IsLocalization.lift_eq _ b

theorem comp_toAway_eq (r : B) (y : PrimeSpectrum B) (g : Localization.Away r →ₐ[𝒪] locRing B y)
    (hg : ∀ b : B, g (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B y) b) :
    g.comp (toAway (𝒪 := 𝒪) r) = toLocRing B y := by
  ext b
  exact hg b

theorem span_image_rTensor_span {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B') (M : FullLattice 𝒪 K)
    (S : Set (latticeBaseChange 𝒪 K B M)) :
    Submodule.span B' ((LinearMap.rTensor (↥M.1) f.toLinearMap) '' (Submodule.span B S : Set (latticeBaseChange 𝒪 K B M))) =
      Submodule.span B' ((LinearMap.rTensor (↥M.1) f.toLinearMap) '' S) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    induction hz using Submodule.span_induction with
    | mem w hw => exact Submodule.subset_span ⟨w, hw, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add u w _ _ hu hw => rw [map_add]; exact Submodule.add_mem _ hu hw
    | smul b w _ hw =>
      rw [rTensor_smul_left f M b w]
      exact Submodule.smul_mem _ _ hw
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem lineBaseChange_toLocRing_eq (r : B) (y : PrimeSpectrum B) (g : Localization.Away r →ₐ[𝒪] locRing B y)
    (hg : ∀ b : B, g (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B y) b)
    (L : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B L)) :
    lineBaseChange (toLocRing B y) L N = lineBaseChange g L (awaySub r L N) := by
  have hfun : (⇑(awayMap (𝒪 := 𝒪) (K := K) r L) : latticeBaseChange 𝒪 K B L → latticeBaseChange 𝒪 K (Localization.Away r) L) =
      ⇑(LinearMap.rTensor (↥L.1) (toAway (𝒪 := 𝒪) r).toLinearMap) :=
    funext fun z => awayMap_apply r L z
  rw [awaySub, Submodule.localized'_eq_span, hfun, lineBaseChange, lineBaseChange, span_image_rTensor_span,
    ← Set.image_comp]
  congr 1
  refine Set.image_congr fun z _ => ?_
  change LinearMap.rTensor (↥L.1) (toLocRing B y).toLinearMap z =
    LinearMap.rTensor (↥L.1) g.toLinearMap (LinearMap.rTensor (↥L.1) (toAway (𝒪 := 𝒪) r).toLinearMap z)
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  congr 2
  rw [← comp_toAway_eq r y g hg]
  rfl

theorem lineBaseChange_toLocRing_eq_localized' (x : PrimeSpectrum B) (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) :
    lineBaseChange (toLocRing B x) M N = N.localized' (locRing B x) x.asIdeal.primeCompl (locMap x M) := by
  have hfun : (⇑(LinearMap.rTensor (↥M.1) (toLocRing B x).toLinearMap) :
      latticeBaseChange 𝒪 K B M → latticeBaseChange 𝒪 K (locRing B x) M) = ⇑(locMap x M) :=
    funext fun z => (locMap_apply x M z).symm
  rw [Submodule.localized'_eq_span, lineBaseChange, hfun]

theorem ext_one_tmul {C : Type} [CommRing C] [Algebra 𝒪 C] {L : FullLattice 𝒪 K} {X : Type} [AddCommGroup X] [Module C X]
    {f g : latticeBaseChange 𝒪 K C L →ₗ[C] X} (h : ∀ w : ↥L.1, f ((1 : C) ⊗ₜ[𝒪] w) = g ((1 : C) ⊗ₜ[𝒪] w)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b w =>
      have hb : b ⊗ₜ[𝒪] w = b • ((1 : C) ⊗ₜ[𝒪] w) := by rw [smul_tmul', smul_eq_mul, mul_one]
      rw [hb, map_smul, map_smul, h w]

theorem rTensor_smulIntoBaseChange {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B') {M' M : FullLattice 𝒪 K}
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) (z : latticeBaseChange 𝒪 K B M) :
    LinearMap.rTensor (↥M'.1) f.toLinearMap
        (((smulInto π hπM).baseChange B : latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K B M') z) =
      ((smulInto π hπM).baseChange B' : latticeBaseChange 𝒪 K B' M →ₗ[B'] latticeBaseChange 𝒪 K B' M')
        (LinearMap.rTensor (↥M.1) f.toLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b v => rw [LinearMap.baseChange_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, LinearMap.baseChange_tmul]

end Loc

section Primes

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

def pt (r : B) (𝔮 : Ideal (Localization.Away r)) [𝔮.IsPrime] : PrimeSpectrum B :=
  ⟨𝔮.comap (algebraMap B (Localization.Away r)), Ideal.IsPrime.comap _⟩

theorem mem_pt_iff (r : B) (𝔮 : Ideal (Localization.Away r)) [𝔮.IsPrime] (b : B) :
    b ∈ (pt r 𝔮).asIdeal ↔ algebraMap B (Localization.Away r) b ∈ 𝔮 := Ideal.mem_comap

theorem not_mem_pt (r : B) (𝔮 : Ideal (Localization.Away r)) [h𝔮 : 𝔮.IsPrime] : r ∉ (pt r 𝔮).asIdeal := by
  rw [mem_pt_iff]
  intro h
  exact h𝔮.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.map_units _ ⟨r, Submonoid.mem_powers r⟩))

theorem map_mem_maximalIdeal (r : B) (𝔮 : Ideal (Localization.Away r)) [h𝔮 : 𝔮.IsPrime]
    (g : Localization.Away r →ₐ[𝒪] locRing B (pt r 𝔮))
    (hg : ∀ b : B, g (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B (pt r 𝔮)) b)
    (q : Localization.Away r) (hq : q ∈ 𝔮) : g q ∈ IsLocalRing.maximalIdeal (locRing B (pt r 𝔮)) := by
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) q
  have h1 : b ∈ (pt r 𝔮).asIdeal := by
    rw [mem_pt_iff, ← IsLocalization.mk'_spec (Localization.Away r) b s]
    exact 𝔮.mul_mem_right _ hq
  have h2 : g (IsLocalization.mk' _ b s) * g (algebraMap B _ (s : B)) = algebraMap B (locRing B (pt r 𝔮)) b := by
    rw [← map_mul, IsLocalization.mk'_spec, hg]
  have h3 : algebraMap B (locRing B (pt r 𝔮)) b ∈ IsLocalRing.maximalIdeal (locRing B (pt r 𝔮)) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (locRing B (pt r 𝔮)) (pt r 𝔮).asIdeal b).mpr h1
  rw [← h2] at h3
  rcases (IsLocalRing.maximalIdeal.isMaximal (locRing B (pt r 𝔮))).isPrime.mem_or_mem h3 with h | h
  · exact h
  · exfalso
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have hs : (s : B) ∉ (pt r 𝔮).asIdeal := by
      rw [← hn]
      exact fun h' => not_mem_pt r 𝔮 ((pt r 𝔮).2.mem_of_pow_mem n h')
    rw [hg] at h
    exact (IsLocalRing.mem_maximalIdeal _).mp h (IsLocalization.map_units (locRing B (pt r 𝔮)) (⟨s, hs⟩ : (pt r 𝔮).asIdeal.primeCompl))

theorem rTensor_mem_sup (r : B) (𝔮 : Ideal (Localization.Away r)) [h𝔮 : 𝔮.IsPrime]
    (g : Localization.Away r →ₐ[𝒪] locRing B (pt r 𝔮))
    (hg : ∀ b : B, g (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B (pt r 𝔮)) b)
    (L : FullLattice 𝒪 K) (P : Submodule (Localization.Away r) (latticeBaseChange 𝒪 K (Localization.Away r) L))
    (z : latticeBaseChange 𝒪 K (Localization.Away r) L)
    (hz : z ∈ P ⊔ (𝔮 • ⊤ : Submodule (Localization.Away r) (latticeBaseChange 𝒪 K (Localization.Away r) L))) :
    LinearMap.rTensor (↥L.1) g.toLinearMap z ∈ lineBaseChange g L P ⊔
      (IsLocalRing.maximalIdeal (locRing B (pt r 𝔮)) • ⊤ :
        Submodule (locRing B (pt r 𝔮)) (latticeBaseChange 𝒪 K (locRing B (pt r 𝔮)) L)) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
  rw [map_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨a, ha, rfl⟩)) (Submodule.mem_sup_right ?_)
  refine Submodule.smul_induction_on
    (p := fun b => LinearMap.rTensor (↥L.1) g.toLinearMap b ∈ (IsLocalRing.maximalIdeal (locRing B (pt r 𝔮)) • ⊤ :
        Submodule (locRing B (pt r 𝔮)) (latticeBaseChange 𝒪 K (locRing B (pt r 𝔮)) L))) hb ?_ ?_
  · intro q hq w _
    rw [rTensor_smul_left g L q w]
    exact Submodule.smul_mem_smul (map_mem_maximalIdeal r 𝔮 g hg q hq) Submodule.mem_top
  · intro u w hu hw
    rw [map_add]
    exact Submodule.add_mem _ hu hw

variable {T : Type} [AddCommGroup T] [Module B T]

theorem mem_ideal_smul_top_of_mem_maximalIdeal_smul_top (y : PrimeSpectrum B) (t : stalk B y T)
    (ht : t ∈ (IsLocalRing.maximalIdeal (locRing B y) • ⊤ : Submodule (locRing B y) (stalk B y T))) :
    t ∈ (y.asIdeal • ⊤ : Submodule B (stalk B y T)) := by
  induction ht using Submodule.smul_induction_on' with
  | smul q hq t _ =>
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective y.asIdeal.primeCompl q
    have hb : b ∈ y.asIdeal := (IsLocalization.AtPrime.mk'_mem_maximal_iff (locRing B y) y.asIdeal b s).mp hq
    have e : IsLocalization.mk' (locRing B y) b s • t = b • (IsLocalization.mk' (locRing B y) (1 : B) s • t) := by
      rw [← smul_assoc, Algebra.smul_def b (IsLocalization.mk' (locRing B y) (1 : B) s), ← IsLocalization.mk'_eq_mul_mk'_one]
    rw [e]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb

theorem apply_mem_smul_top_of_mem_ker_sup {C : Type} [CommRing C] {V W : Type} [AddCommGroup V] [Module C V]
    [AddCommGroup W] [Module C W] (f : V →ₗ[C] W) (I : Ideal C) (w : V)
    (hw : w ∈ LinearMap.ker f ⊔ (I • ⊤ : Submodule C V)) : f w ∈ (I • ⊤ : Submodule C W) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add, LinearMap.mem_ker.mp ha, zero_add]
  have : f b ∈ (I • ⊤ : Submodule C V).map f := Submodule.mem_map_of_mem hb
  rw [Submodule.map_smul'', Submodule.map_top] at this
  exact Submodule.smul_mono le_rfl le_top this

theorem mem_smul_top_of_map_mem {C : Type} [CommRing C] {V W : Type} [AddCommGroup V] [Module C V] [AddCommGroup W]
    [Module C W] (f : V →ₗ[C] W) (hf : Function.Bijective f) (I : Ideal C) (m : V)
    (hm : f m ∈ (I • ⊤ : Submodule C W)) : m ∈ (I • ⊤ : Submodule C V) := by
  let e : V ≃ₗ[C] W := LinearEquiv.ofBijective f hf
  have h1 : (I • ⊤ : Submodule C W) = (I • ⊤ : Submodule C V).map e.toLinearMap := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  have h2 : f m = e m := rfl
  rw [h1, h2] at hm
  obtain ⟨m', hm', he⟩ := hm
  rw [LinearEquiv.coe_coe, e.injective.eq_iff] at he
  rwa [← he]

end Primes

section Key

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {T : Type} [AddCommGroup T] [Module B T]

theorem lineBaseChange_awaySub_ker_eq (r : B) (y : PrimeSpectrum B) (hy : r ∉ y.asIdeal)
    (g : Localization.Away r →ₐ[𝒪] locRing B y)
    (hg : ∀ b : B, g (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B y) b)
    (L : FullLattice 𝒪 K) (A : latticeBaseChange 𝒪 K B L →ₗ[B] T)
    (u : latticeBaseChange 𝒪 K (locRing B y) L →ₗ[locRing B y] stalk B y T)
    (h : ∀ v : ↥L.1, (LocalizedModule.mk (A ((1 : B) ⊗ₜ[𝒪] v)) 1 : stalk B y T) =
      algebraMap B (locRing B y) r • u ((1 : locRing B y) ⊗ₜ[𝒪] v)) :
    lineBaseChange g L (awaySub r L (LinearMap.ker A)) = LinearMap.ker u := by
  rw [← lineBaseChange_toLocRing_eq r y g hg, lineBaseChange_toLocRing_eq_localized',
    LinearMap.localized'_ker_eq_ker_localizedMap (locRing B y) y.asIdeal.primeCompl (locMap y L)
      (LocalizedModule.mkLinearMap y.asIdeal.primeCompl T) A]
  set Ay : latticeBaseChange 𝒪 K (locRing B y) L →ₗ[locRing B y] stalk B y T :=
    (IsLocalizedModule.map y.asIdeal.primeCompl (locMap y L) (LocalizedModule.mkLinearMap y.asIdeal.primeCompl T) A
      ).extendScalarsOfIsLocalization y.asIdeal.primeCompl (locRing B y)
  have hAy : Ay = algebraMap B (locRing B y) r • u := by
    apply ext_one_tmul
    intro v
    rw [LinearMap.smul_apply, ← h v, LinearMap.extendScalarsOfIsLocalization_apply', ← locMap_one_tmul y L v,
      IsLocalizedModule.map_apply, LocalizedModule.mkLinearMap_apply]
  rw [hAy]
  have hu : IsUnit (algebraMap B (locRing B y) r) := IsLocalization.map_units (locRing B y) (⟨r, hy⟩ : y.asIdeal.primeCompl)
  ext w
  rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.smul_apply]
  constructor
  · intro h0
    exact hu.smul_left_cancel.mp (h0.trans (smul_zero _).symm)
  · intro h0
    rw [h0, smul_zero]

theorem invertible_quot_awaySub_ker [Module.Invertible B T] (r : B) (L : FullLattice 𝒪 K)
    (A : latticeBaseChange 𝒪 K B L →ₗ[B] T) (hs : ∀ t : T, ∃ (w : latticeBaseChange 𝒪 K B L) (n : ℕ), A w = r ^ n • t) :
    Module.Invertible (Localization.Away r)
      (latticeBaseChange 𝒪 K (Localization.Away r) L ⧸ awaySub r L (LinearMap.ker A)) := by
  rw [awaySub, LinearMap.localized'_ker_eq_ker_localizedMap (Localization.Away r) (Submonoid.powers r) (awayMap r L)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) T) A]
  set Ar : latticeBaseChange 𝒪 K (Localization.Away r) L →ₗ[Localization.Away r]
      LocalizedModule (Submonoid.powers r) T :=
    (IsLocalizedModule.map (Submonoid.powers r) (awayMap r L) (LocalizedModule.mkLinearMap (Submonoid.powers r) T) A
      ).extendScalarsOfIsLocalization (Submonoid.powers r) (Localization.Away r)
  have hsurj : Function.Surjective Ar := by
    intro τ
    induction τ using LocalizedModule.induction_on with
    | h t s =>
      obtain ⟨w, n, hw⟩ := hs t
      refine ⟨(Localization.mk 1 (s * ⟨r ^ n, n, rfl⟩)) • awayMap r L w, ?_⟩
      rw [LinearMap.map_smul, LinearMap.extendScalarsOfIsLocalization_apply', IsLocalizedModule.map_apply,
        LocalizedModule.mkLinearMap_apply, hw, LocalizedModule.mk_smul_mk, one_smul, LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      rw [one_smul, one_smul, mul_one, Submonoid.smul_def, Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
  exact Module.Invertible.congr (LinearMap.quotKerEquivOfSurjective Ar hsurj).symm

theorem map_incl_awaySub_le (r : B) (M' M : FullLattice 𝒪 K) (hle : M'.1 ≤ M.1)
    (N' : Submodule B (latticeBaseChange 𝒪 K B M')) (N : Submodule B (latticeBaseChange 𝒪 K B M))
    (h : N'.map (inclBaseChange B hle) ≤ N) :
    (awaySub r M' N').map (inclBaseChange (Localization.Away r) hle) ≤ awaySub r M N := by
  rw [awaySub, awaySub, Submodule.localized'_eq_span, Submodule.localized'_eq_span, Submodule.map_span, ← Set.image_comp]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨n, hn, rfl⟩
  refine Submodule.subset_span ⟨inclBaseChange B hle n, h ⟨n, hn, rfl⟩, ?_⟩
  show awayMap r M (inclBaseChange B hle n) = inclBaseChange (Localization.Away r) hle (awayMap r M' n)
  rw [awayMap_apply, awayMap_apply, rTensor_inclBaseChange]

theorem map_smul_awaySub_le (r : B) (M' M : FullLattice 𝒪 K) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (N' : Submodule B (latticeBaseChange 𝒪 K B M')) (N : Submodule B (latticeBaseChange 𝒪 K B M))
    (h : N.map ((smulInto π hπM).baseChange B :
      latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K B M') ≤ N') :
    (awaySub r M N).map ((smulInto π hπM).baseChange (Localization.Away r) :
      latticeBaseChange 𝒪 K (Localization.Away r) M →ₗ[Localization.Away r]
        latticeBaseChange 𝒪 K (Localization.Away r) M') ≤ awaySub r M' N' := by
  rw [awaySub, awaySub, Submodule.localized'_eq_span, Submodule.localized'_eq_span, Submodule.map_span, ← Set.image_comp]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨n, hn, rfl⟩
  refine Submodule.subset_span ⟨(smulInto π hπM).baseChange B n, h ⟨n, hn, rfl⟩, ?_⟩
  show awayMap r M' ((smulInto π hπM).baseChange B n) =
    ((smulInto π hπM).baseChange (Localization.Away r) : latticeBaseChange 𝒪 K (Localization.Away r) M →ₗ[Localization.Away r]
        latticeBaseChange 𝒪 K (Localization.Away r) M') (awayMap r M n)
  rw [awayMap_apply, awayMap_apply, rTensor_smulIntoBaseChange]

end Key

section Quadruple

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem mem_N₀_of_u₁_mem (Q : DrinfeldDatum (K := K) π B) (y : PrimeSpectrum B) (v : ↥(Q.N₁ y))
    (h : Q.u₁ y ((1 : locRing B y) ⊗ₜ[𝒪] v) ∈
      (IsLocalRing.maximalIdeal (locRing B y) • ⊤ : Submodule (locRing B y) (stalk B y Q.T₁))) :
    (v : Fin 2 → K) ∈ Q.N₀ y :=
  Q.injective₁ y v (Submodule.mem_sup_right (mem_ideal_smul_top_of_mem_maximalIdeal_smul_top y _ h))

theorem exists_of_u₀_mem (Q : DrinfeldDatum (K := K) π B) (y : PrimeSpectrum B) (v : ↥(Q.N₀ y))
    (h : Q.u₀ y ((1 : locRing B y) ⊗ₜ[𝒪] v) ∈
      (IsLocalRing.maximalIdeal (locRing B y) • ⊤ : Submodule (locRing B y) (stalk B y Q.T₀))) :
    ∃ w ∈ Q.N₁ y, (v : Fin 2 → K) = algebraMap 𝒪 K π • w :=
  Q.injective₀ y v (Submodule.mem_sup_right (mem_ideal_smul_top_of_mem_maximalIdeal_smul_top y _ h))

theorem exists_of_u₁_mem_of_bijective (Q : DrinfeldDatum (K := K) π B) (y : PrimeSpectrum B)
    (hb : Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl Q.Pi₀)) (v : ↥(Q.N₀ y))
    (h : Q.u₁ y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, Q.le y v.2⟩ : ↥(Q.N₁ y))) ∈
      (IsLocalRing.maximalIdeal (locRing B y) • ⊤ : Submodule (locRing B y) (stalk B y Q.T₁))) :
    ∃ w ∈ Q.N₁ y, (v : Fin 2 → K) = algebraMap 𝒪 K π • w := by
  have e := Q.u₁_incl y ((1 : locRing B y) ⊗ₜ[𝒪] v)
  change Q.u₁ y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, Q.le y v.2⟩ : ↥(Q.N₁ y))) = _ at e
  rw [e] at h
  exact exists_of_u₀_mem Q y v (mem_smul_top_of_map_mem _ hb _ _ h)

theorem mem_N₀_of_u₀_mem_of_bijective (Q : DrinfeldDatum (K := K) π B) (y : PrimeSpectrum B)
    (hb : Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl Q.Pi₁)) (w : ↥(Q.N₁ y)) (v : ↥(Q.N₀ y))
    (hv : (v : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K))
    (h : Q.u₀ y ((1 : locRing B y) ⊗ₜ[𝒪] v) ∈
      (IsLocalRing.maximalIdeal (locRing B y) • ⊤ : Submodule (locRing B y) (stalk B y Q.T₀))) :
    (w : Fin 2 → K) ∈ Q.N₀ y := by
  have hv' : v = smulInto π (Q.smul_le y) w := Subtype.ext hv
  subst hv'
  have e := Q.u₀_smul y ((1 : locRing B y) ⊗ₜ[𝒪] w)
  rw [LinearMap.baseChange_tmul] at e
  rw [e] at h
  exact mem_N₀_of_u₁_mem Q y w (mem_smul_top_of_map_mem _ hb _ _ h)

theorem ker_eq_line_of_eq {C : Type} [CommRing C] [Algebra 𝒪 C] (D : DeligneDatum (K := K) π C) (M : FullLattice 𝒪 K)
    (L : Submodule 𝒪 (Fin 2 → K)) (hL : IsFullLattice L) {X : Type} [AddCommGroup X] [Module C X]
    (u : latticeBaseChange 𝒪 K C ⟨L, hL⟩ →ₗ[C] X) (hML : M.1 ≤ L)
    (e : D.line M = LinearMap.ker (u ∘ₗ inclBaseChange C (M' := M) (M := ⟨L, hL⟩) hML)) (hLM : L = M.1) :
    LinearMap.ker u = D.line ⟨L, hL⟩ := by
  subst hLM
  have hincl : inclBaseChange C (M' := M) (M := ⟨M.1, hL⟩) hML = LinearMap.id :=
    ext_one_tmul fun w => rfl
  rw [hincl, LinearMap.comp_id] at e
  exact e.symm

theorem line_act_eq_of_line_eq {C : Type} [CommRing C] [Algebra 𝒪 C] (D D' : DeligneDatum (K := K) π C) (c : Kˣ)
    (L : FullLattice 𝒪 K) (e : D.line L = D'.line L) :
    D.line (FullLattice.act (scalarGL c) L) = D'.line (FullLattice.act (scalarGL c) L) := by
  rw [D.homothety, D'.homothety, e]

theorem L₁_eq_act (Q : DrinfeldDatum (K := K) π B) (x y : PrimeSpectrum B) (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    (e₀ : Q.N₀ y = Q.N₀ x) (e₁ : ∀ v : Fin 2 → K, v ∈ Q.N₁ y ↔ algebraMap 𝒪 K π • v ∈ Q.N₀ x) :
    Q.L₁ y = FullLattice.act (scalarGL c⁻¹) (Q.L₀ y) := by
  apply Subtype.ext
  show Q.N₁ y = latticeMap (scalarGL c⁻¹) (Q.N₀ y)
  ext v
  rw [e₁ v, mem_latticeMap_scalarGL, e₀]
  constructor
  · intro hv
    refine ⟨algebraMap 𝒪 K π • v, hv, ?_⟩
    rw [← hc, smul_smul, Units.inv_mul, one_smul]
  · rintro ⟨w, hw, rfl⟩
    rwa [← hc, smul_smul, Units.mul_inv, one_smul]

theorem main (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π))
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    ∃ r : B, r ∉ x.asIdeal ∧ ∃ d : DeligneDatum (K := K) π (Localization.Away r),
      ∀ (y : PrimeSpectrum B), r ∉ y.asIdeal →
        ∀ g : Localization.Away r →ₐ[𝒪] locRing B y,
          (∀ b : B, g (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B y) b) →
          LinearMap.ker (Q.u₀ y) = (d.map π g).line (Q.L₀ y) ∧ LinearMap.ker (Q.u₁ y) = (d.map π g).line (Q.L₁ y) ∧
            (d.map π g).InEdgeChart π (Q.L₀ y) (Q.L₁ y) := by

  obtain ⟨U, hU, hxU, hUty⟩ :=
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isOpen_forall_lattice_eq_or_bijective_map hπ hB Q x
  obtain ⟨_, ⟨r₀, rfl⟩, hxr₀, hr₀U⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU hU
  have hr₀x : r₀ ∉ x.asIdeal := hxr₀
  have hyU : ∀ y : PrimeSpectrum B, r₀ ∉ y.asIdeal → y ∈ U := fun y hy => hr₀U hy
  have hM0 : ∀ y : PrimeSpectrum B, r₀ ∉ y.asIdeal → Q.N₀ x ≤ Q.N₀ y := fun y hy => (hUty y (hyU y hy)).1
  have hM1 : ∀ y : PrimeSpectrum B, r₀ ∉ y.asIdeal → Q.N₁ x ≤ Q.N₁ y := fun y hy => (hUty y (hyU y hy)).2.1

  obtain ⟨r, hrx, hr₀r, A₀, A₁, hc₀, hc₁, hA₀, hA₁, hA₀s, hA₁s⟩ :=
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_compatible_linearMap_pair_mk_tmul_eq_smul Q x r₀ hr₀x hM0 hM1
  have hr₀_of : ∀ y : PrimeSpectrum B, r ∉ y.asIdeal → r₀ ∉ y.asIdeal := fun y hy h => by
    obtain ⟨c, hc⟩ := hr₀r
    exact hy (hc ▸ y.asIdeal.mul_mem_right c h)
  haveI : Module.Invertible (Localization.Away r)
      (latticeBaseChange 𝒪 K (Localization.Away r) (Q.L₁ x) ⧸ awaySub r (Q.L₁ x) (LinearMap.ker A₁)) :=
    invertible_quot_awaySub_ker r (Q.L₁ x) A₁ hA₁s
  haveI : Module.Invertible (Localization.Away r)
      (latticeBaseChange 𝒪 K (Localization.Away r) (Q.L₀ x) ⧸ awaySub r (Q.L₀ x) (LinearMap.ker A₀)) :=
    invertible_quot_awaySub_ker r (Q.L₀ x) A₀ hA₀s
  have hmono : (awaySub r (Q.L₀ x) (LinearMap.ker A₀)).map (inclBaseChange (Localization.Away r) (Q.le x)) ≤
      awaySub r (Q.L₁ x) (LinearMap.ker A₁) := by
    refine map_incl_awaySub_le r (Q.L₀ x) (Q.L₁ x) (Q.le x) (LinearMap.ker A₀) (LinearMap.ker A₁) ?_
    rintro _ ⟨n, hn, rfl⟩
    have hn' : A₀ n = 0 := hn
    show A₁ (inclBaseChange B (Q.le x) n) = 0
    rw [hc₀, hn', map_zero]
  have hsmul : (awaySub r (Q.L₁ x) (LinearMap.ker A₁)).map ((smulInto π (Q.smul_le x)).baseChange (Localization.Away r) :
      latticeBaseChange 𝒪 K (Localization.Away r) (Q.L₁ x) →ₗ[Localization.Away r]
        latticeBaseChange 𝒪 K (Localization.Away r) (Q.L₀ x)) ≤ awaySub r (Q.L₀ x) (LinearMap.ker A₀) := by
    refine map_smul_awaySub_le π r (Q.L₀ x) (Q.L₁ x) (Q.smul_le x) (LinearMap.ker A₀) (LinearMap.ker A₁) ?_
    rintro _ ⟨n, hn, rfl⟩
    have hn' : A₁ n = 0 := hn
    show A₀ ((smulInto π (Q.smul_le x)).baseChange B n) = 0
    rw [hc₁, hn', map_zero]

  have key₁ : ∀ (y : PrimeSpectrum B) (hy : r ∉ y.asIdeal) (g : Localization.Away r →ₐ[𝒪] locRing B y)
      (hg : ∀ b : B, g (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B y) b),
      lineBaseChange g (Q.L₁ x) (awaySub r (Q.L₁ x) (LinearMap.ker A₁)) =
        LinearMap.ker (Q.u₁ y ∘ₗ inclBaseChange (locRing B y) (M' := Q.L₁ x) (M := Q.L₁ y) (hM1 y (hr₀_of y hy))) :=
    fun y hy g hg => lineBaseChange_awaySub_ker_eq r y hy g hg (Q.L₁ x) A₁ _ fun v => hA₁ y (hr₀_of y hy) hy v
  have key₀ : ∀ (y : PrimeSpectrum B) (hy : r ∉ y.asIdeal) (g : Localization.Away r →ₐ[𝒪] locRing B y)
      (hg : ∀ b : B, g (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B y) b),
      lineBaseChange g (Q.L₀ x) (awaySub r (Q.L₀ x) (LinearMap.ker A₀)) =
        LinearMap.ker (Q.u₀ y ∘ₗ inclBaseChange (locRing B y) (M' := Q.L₀ x) (M := Q.L₀ y) (hM0 y (hr₀_of y hy))) :=
    fun y hy g hg => lineBaseChange_awaySub_ker_eq r y hy g hg (Q.L₀ x) A₀ _ fun v => hA₀ y (hr₀_of y hy) hy v

  have h₁ : ∀ 𝔮 : Ideal (Localization.Away r), 𝔮.IsPrime → ∀ v : ↥(Q.L₁ x).1, (v : Fin 2 → K) ∉ (Q.L₀ x).1 →
      (1 : Localization.Away r) ⊗ₜ[𝒪] v ∉ awaySub r (Q.L₁ x) (LinearMap.ker A₁) ⊔
        (𝔮 • ⊤ : Submodule (Localization.Away r) (latticeBaseChange 𝒪 K (Localization.Away r) (Q.L₁ x))) := by
    intro 𝔮 h𝔮 v hvM' hmem
    have hry : r ∉ (pt r 𝔮).asIdeal := not_mem_pt r 𝔮
    have hr₀y : r₀ ∉ (pt r 𝔮).asIdeal := hr₀_of _ hry
    have hg := awayToLoc_algebraMap (𝒪 := 𝒪) r (pt r 𝔮) hry
    have h1 := rTensor_mem_sup r 𝔮 (awayToLoc r (pt r 𝔮) hry) hg (Q.L₁ x) _ _ hmem
    rw [rTensor_one_tmul, key₁ (pt r 𝔮) hry _ hg] at h1
    have h2 := apply_mem_smul_top_of_mem_ker_sup _ _ _ h1
    change Q.u₁ (pt r 𝔮) ((1 : locRing B (pt r 𝔮)) ⊗ₜ[𝒪] (⟨v, hM1 _ hr₀y v.2⟩ : ↥(Q.N₁ (pt r 𝔮)))) ∈ _ at h2
    have h3 : (v : Fin 2 → K) ∈ Q.N₀ (pt r 𝔮) := mem_N₀_of_u₁_mem Q _ _ h2
    rcases (hUty _ (hyU _ hr₀y)).2.2 with ⟨e₀, e₁⟩ | ⟨hb, e₀, e₁⟩ | ⟨hb, e₀, e₁⟩
    · rw [e₀] at h3
      exact hvM' h3
    · obtain ⟨w, hw, hvw⟩ := exists_of_u₁_mem_of_bijective Q _ hb ⟨v, h3⟩ h2
      rw [e₁] at hw
      exact hvM' (hvw ▸ Q.smul_le x w hw)
    · rw [e₀] at h3
      exact hvM' h3
  have h₂ : ∀ 𝔮 : Ideal (Localization.Away r), 𝔮.IsPrime → ∀ v' : ↥(Q.L₀ x).1,
      (¬ ∃ w : ↥(Q.L₁ x).1, (v' : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K)) →
      (1 : Localization.Away r) ⊗ₜ[𝒪] v' ∉ awaySub r (Q.L₀ x) (LinearMap.ker A₀) ⊔
        (𝔮 • ⊤ : Submodule (Localization.Away r) (latticeBaseChange 𝒪 K (Localization.Away r) (Q.L₀ x))) := by
    intro 𝔮 h𝔮 v' hv' hmem
    have hry : r ∉ (pt r 𝔮).asIdeal := not_mem_pt r 𝔮
    have hr₀y : r₀ ∉ (pt r 𝔮).asIdeal := hr₀_of _ hry
    have hg := awayToLoc_algebraMap (𝒪 := 𝒪) r (pt r 𝔮) hry
    have h1 := rTensor_mem_sup r 𝔮 (awayToLoc r (pt r 𝔮) hry) hg (Q.L₀ x) _ _ hmem
    rw [rTensor_one_tmul, key₀ (pt r 𝔮) hry _ hg] at h1
    have h2 := apply_mem_smul_top_of_mem_ker_sup _ _ _ h1
    change Q.u₀ (pt r 𝔮) ((1 : locRing B (pt r 𝔮)) ⊗ₜ[𝒪] (⟨v', hM0 _ hr₀y v'.2⟩ : ↥(Q.N₀ (pt r 𝔮)))) ∈ _ at h2
    obtain ⟨w, hw, hvw⟩ := exists_of_u₀_mem Q _ _ h2
    rcases (hUty _ (hyU _ hr₀y)).2.2 with ⟨e₀, e₁⟩ | ⟨hb, e₀, e₁⟩ | ⟨hb, e₀, e₁⟩
    · rw [e₁] at hw
      exact hv' ⟨⟨w, hw⟩, hvw⟩
    · rw [e₁] at hw
      exact hv' ⟨⟨w, hw⟩, hvw⟩
    · have h4 : w ∈ Q.N₀ (pt r 𝔮) := mem_N₀_of_u₀_mem_of_bijective Q _ hb ⟨w, hw⟩ _ hvw h2
      rw [e₀] at h4
      exact hv' ⟨⟨w, Q.le x h4⟩, hvw⟩

  obtain ⟨d, hdM, hdM', hchart⟩ :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.exists_inEdgeChart_and_line_eq (K := K) hπ (B := Localization.Away r)
      (M' := Q.L₀ x) (M := Q.L₁ x) (Q.le x) (Q.smul_le x) (awaySub r (Q.L₁ x) (LinearMap.ker A₁))
      (awaySub r (Q.L₀ x) (LinearMap.ker A₀)) hmono hsmul h₁ h₂

  refine ⟨r, hrx, d, fun y hry g hg => ?_⟩
  have hr₀y : r₀ ∉ y.asIdeal := hr₀_of y hry
  obtain ⟨dy, hk₀, hk₁, hch⟩ := CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_localDeligneDatum hπ Q y

  have eM : (d.map π g).line (Q.L₁ x) = LinearMap.ker (Q.u₁ y ∘ₗ inclBaseChange (locRing B y) (M' := Q.L₁ x)
      (M := Q.L₁ y) (hM1 y hr₀y)) := by
    show lineBaseChange g (Q.L₁ x) (d.line (Q.L₁ x)) = _
    rw [hdM]
    exact key₁ y hry g hg
  have eM' : (d.map π g).line (Q.L₀ x) = LinearMap.ker (Q.u₀ y ∘ₗ inclBaseChange (locRing B y) (M' := Q.L₀ x)
      (M := Q.L₀ y) (hM0 y hr₀y)) := by
    show lineBaseChange g (Q.L₀ x) (d.line (Q.L₀ x)) = _
    rw [hdM']
    exact key₀ y hry g hg

  have hagree : (d.map π g).line (Q.L₀ y) = dy.line (Q.L₀ y) ∧ (d.map π g).line (Q.L₁ y) = dy.line (Q.L₁ y) := by
    rcases (hUty y (hyU y hr₀y)).2.2 with ⟨e₀, e₁⟩ | ⟨hb, e₀, e₁⟩ | ⟨hb, e₀, e₁⟩
    · have k₀ := ker_eq_line_of_eq (d.map π g) (Q.L₀ x) (Q.N₀ y) (Q.full₀ y) (Q.u₀ y) (hM0 y hr₀y) eM' e₀
      have k₁ := ker_eq_line_of_eq (d.map π g) (Q.L₁ x) (Q.N₁ y) (Q.full₁ y) (Q.u₁ y) (hM1 y hr₀y) eM e₁
      exact ⟨by rw [← k₀, hk₀], by rw [← k₁, hk₁]⟩
    · have k₁ := ker_eq_line_of_eq (d.map π g) (Q.L₁ x) (Q.N₁ y) (Q.full₁ y) (Q.u₁ y) (hM1 y hr₀y) eM e₁
      have hL : Q.L₀ y = Q.L₁ y := Subtype.ext (e₀.trans e₁.symm)
      have a₁ : (d.map π g).line (Q.L₁ y) = dy.line (Q.L₁ y) := by rw [← k₁, hk₁]
      refine ⟨?_, a₁⟩
      rw [hL]
      exact a₁
    · have k₀ := ker_eq_line_of_eq (d.map π g) (Q.L₀ x) (Q.N₀ y) (Q.full₀ y) (Q.u₀ y) (hM0 y hr₀y) eM' e₀
      have a₀ : (d.map π g).line (Q.L₀ y) = dy.line (Q.L₀ y) := by rw [← k₀, hk₀]
      refine ⟨a₀, ?_⟩
      have hπK : algebraMap 𝒪 K π ≠ 0 := fun h =>
        hπ.ne_zero ((injective_iff_map_eq_zero (algebraMap 𝒪 K)).mp (IsFractionRing.injective 𝒪 K) π h)
      have hL := L₁_eq_act Q x y (Units.mk0 _ hπK) rfl e₀ e₁
      rw [hL]
      exact line_act_eq_of_line_eq _ _ _ _ a₀

  have hdy : d.map π g = dy :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ dy (d.map π g) (Q.L₀ y) (Q.L₁ y) hch
      hagree.2 hagree.1
  rw [hdy]
  exact ⟨hk₀, hk₁, hch⟩

end Quadruple

end P2mKcQuadrupleLocalModel
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_deligneDatum_away_forall_map.P2mKcQuadrupleLocalModel"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_deligneDatum_away_forall_map.P2mKcQuadrupleLocalModel"

open P2mKcQuadrupleLocalModel in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    ∃ r : B, r ∉ x.asIdeal ∧ ∃ d : DeligneDatum (K := K) π (Localization.Away r),
      ∀ (y : PrimeSpectrum B), r ∉ y.asIdeal →
        ∀ g : Localization.Away r →ₐ[𝒪] locRing B y,
          (∀ b : B, g (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B y) b) →
          LinearMap.ker (Q.u₀ y) = (d.map π g).line (Q.L₀ y) ∧ LinearMap.ker (Q.u₁ y) = (d.map π g).line (Q.L₁ y) ∧
            (d.map π g).InEdgeChart π (Q.L₀ y) (Q.L₁ y) :=
  main hπ hB Q x

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_deligneDatum_away_forall_map
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_deligneDatum_away_forall_map (solution)
