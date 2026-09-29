-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finset_forall_map_eq_iff_of_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/eb917ca8-5196-57ae-bffd-dfeee0d4b420

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finset_forall_map_eq_iff_of_map_eq

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct Pointwise
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega TensorProduct

noncomputable section

namespace P2mKcOmegaDiag

section Openness

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem exists_finset_reps (hfin : Finite (𝒪 ⧸ Ideal.span {π})) (P : FullLattice 𝒪 K) :
    ∃ T : Finset ↥P.1, ∀ v : ↥P.1, ∃ t ∈ T, ∃ w : ↥P.1, v = t + π • w := by
  classical
  set I : Ideal 𝒪 := Ideal.span {π} with hI
  haveI : Module.Finite 𝒪 ↥P.1 := Module.Finite.iff_fg.mpr P.2.1
  haveI : Module.Finite (𝒪 ⧸ I) (↥P.1 ⧸ (I • ⊤ : Submodule 𝒪 ↥P.1)) := inferInstance
  haveI : Finite (↥P.1 ⧸ (I • ⊤ : Submodule 𝒪 ↥P.1)) := Module.finite_of_finite (𝒪 ⧸ I)
  letI : Fintype (↥P.1 ⧸ (I • ⊤ : Submodule 𝒪 ↥P.1)) := Fintype.ofFinite _
  let sec : (↥P.1 ⧸ (I • ⊤ : Submodule 𝒪 ↥P.1)) → ↥P.1 := fun q => (Submodule.Quotient.mk_surjective _ q).choose
  have hsec : ∀ q, Submodule.Quotient.mk (sec q) = q := fun q => (Submodule.Quotient.mk_surjective _ q).choose_spec
  refine ⟨Finset.univ.image sec, fun v => ?_⟩
  refine ⟨sec (Submodule.Quotient.mk v), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have hdiff : v - sec (Submodule.Quotient.mk v) ∈ (I • ⊤ : Submodule 𝒪 ↥P.1) := by
    rw [← Submodule.Quotient.eq, hsec]
  set t := sec (Submodule.Quotient.mk v) with ht
  have hdiff' : v - t ∈ ((Ideal.span {π} : Ideal 𝒪) • ⊤ : Submodule 𝒪 ↥P.1) := hdiff
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hdiff'
  obtain ⟨w, _, hw⟩ := hdiff'
  exact ⟨w, by rw [hw]; abel⟩

theorem one_tmul_add_smul (P : FullLattice 𝒪 K) (t w : ↥P.1) :
    ((1 : B) ⊗ₜ[𝒪] (t + π • w) : latticeBaseChange 𝒪 K B P) =
      (1 : B) ⊗ₜ[𝒪] t + algebraMap 𝒪 B π • ((1 : B) ⊗ₜ[𝒪] w) := by
  rw [tmul_add, tmul_smul, algebraMap_smul]

theorem mem_sup_smul_top_of_mkQ_mem {V : Type} [AddCommGroup V] [Module B V] (N : Submodule B V) (I : Ideal B)
    (x : V) (hx : N.mkQ x ∈ (I • ⊤ : Submodule B (V ⧸ N))) : x ∈ N ⊔ (I • ⊤ : Submodule B V) := by
  have : x ∈ ((I • ⊤ : Submodule B V).map N.mkQ).comap N.mkQ := by
    rw [Submodule.mem_comap, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]; exact hx
  rwa [Submodule.comap_map_mkQ] at this

theorem exists_form_apply_not_mem {V : Type} [AddCommGroup V] [Module B V] (N : Submodule B V)
    [Module.Invertible B (V ⧸ N)] (𝔭 : Ideal B) (x : V) (hx : x ∉ N ⊔ (𝔭 • ⊤ : Submodule B V)) :
    ∃ ψ : V →ₗ[B] B, N ≤ LinearMap.ker ψ ∧ ψ x ∉ 𝔭 := by
  have hq : N.mkQ x ∉ (𝔭 • ⊤ : Submodule B (V ⧸ N)) := fun h => hx (mem_sup_smul_top_of_mkQ_mem N 𝔭 x h)
  obtain ⟨φ, hφ⟩ := exists_linearMap_apply_not_mem 𝔭 (N.mkQ x) hq
  refine ⟨φ ∘ₗ N.mkQ, ?_, hφ⟩
  intro n hn
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr hn, map_zero]

theorem apply_mem_of_mem_sup {V : Type} [AddCommGroup V] [Module B V] {N : Submodule B V} (ψ : V →ₗ[B] B)
    (hψ : N ≤ LinearMap.ker ψ) (𝔮 : Ideal B) (x : V) (hx : x ∈ N ⊔ (𝔮 • ⊤ : Submodule B V)) : ψ x ∈ 𝔮 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, LinearMap.mem_ker.mp (hψ hy), zero_add]
  refine Submodule.smul_induction_on (p := fun z => ψ z ∈ 𝔮) hz (fun r hr n _ => ?_) (fun a b ha hb => ?_)
  · show ψ (r • n) ∈ 𝔮
    rw [map_smul, smul_eq_mul]; exact 𝔮.mul_mem_right _ hr
  · show ψ (a + b) ∈ 𝔮
    rw [map_add]; exact 𝔮.add_mem ha hb

theorem algebraMap_mem_of_isNilpotent (hB : IsNilpotent (algebraMap 𝒪 B π)) (𝔮 : Ideal B) [h𝔮 : 𝔮.IsPrime] :
    algebraMap 𝒪 B π ∈ 𝔮 := by
  obtain ⟨n, hn⟩ := hB
  exact h𝔮.mem_of_pow_mem n (by rw [hn]; exact 𝔮.zero_mem)

theorem one_tmul_mem_sup_of_add (hB : IsNilpotent (algebraMap 𝒪 B π)) (P : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B P)) (𝔮 : Ideal B) [𝔮.IsPrime] (t w : ↥P.1)
    (h : (1 : B) ⊗ₜ[𝒪] (t + π • w) ∈ N ⊔ (𝔮 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B P))) :
    (1 : B) ⊗ₜ[𝒪] t ∈ N ⊔ (𝔮 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B P)) := by
  rw [one_tmul_add_smul] at h
  have hπ : algebraMap 𝒪 B π • ((1 : B) ⊗ₜ[𝒪] w) ∈ N ⊔ (𝔮 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B P)) :=
    Submodule.mem_sup_right (Submodule.smul_mem_smul (algebraMap_mem_of_isNilpotent hB 𝔮) Submodule.mem_top)
  have := Submodule.sub_mem _ h hπ
  rwa [add_sub_cancel_right] at this

theorem prod_not_mem {ι : Type} (s : Finset ι) (ρ : ι → B) (𝔭 : Ideal B) [h𝔭 : 𝔭.IsPrime]
    (h : ∀ i ∈ s, ρ i ∉ 𝔭) : (∏ i ∈ s, ρ i) ∉ 𝔭 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    intro hmem
    rcases h𝔭.mem_or_mem hmem with h1 | h1
    · exact h a (Finset.mem_insert_self a s) h1
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) h1

theorem not_mem_of_prod_not_mem {ι : Type} (s : Finset ι) (ρ : ι → B) (𝔮 : Ideal B) (h : (∏ i ∈ s, ρ i) ∉ 𝔮)
    {i : ι} (hi : i ∈ s) : ρ i ∉ 𝔮 := by
  classical
  intro hmem
  apply h
  rw [← Finset.mul_prod_erase s ρ hi]
  exact 𝔮.mul_mem_right _ hmem

theorem exists_away_of_forall_not_mem (hfin : Finite (𝒪 ⧸ Ideal.span {π})) (hB : IsNilpotent (algebraMap 𝒪 B π))
    (P : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B P)) [Module.Invertible B (latticeBaseChange 𝒪 K B P ⧸ N)]
    (pred : ↥P.1 → Prop) (hpred : ∀ t w : ↥P.1, pred (t + π • w) → pred t)
    (𝔭 : Ideal B) [𝔭.IsPrime]
    (h : ∀ v : ↥P.1, pred v → (1 : B) ⊗ₜ[𝒪] v ∉ N ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B P))) :
    ∃ r : B, r ∉ 𝔭 ∧ ∀ 𝔮 : Ideal B, 𝔮.IsPrime → r ∉ 𝔮 →
      ∀ v : ↥P.1, pred v → (1 : B) ⊗ₜ[𝒪] v ∉ N ⊔ (𝔮 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B P)) := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_reps hfin P
  have hex : ∀ t : ↥P.1, ∃ ρψ : B × (latticeBaseChange 𝒪 K B P →ₗ[B] B), ρψ.1 ∉ 𝔭 ∧
      (pred t → N ≤ LinearMap.ker ρψ.2 ∧ ρψ.2 ((1 : B) ⊗ₜ[𝒪] t) = ρψ.1) := by
    intro t
    by_cases ht : pred t
    · obtain ⟨ψ, hψN, hψt⟩ := exists_form_apply_not_mem N 𝔭 _ (h t ht)
      exact ⟨(ψ ((1 : B) ⊗ₜ[𝒪] t), ψ), hψt, fun _ => ⟨hψN, rfl⟩⟩
    · refine ⟨(1, 0), fun h1 => ‹𝔭.IsPrime›.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun h' => (ht h').elim⟩
  choose ρψ hρψ using hex
  refine ⟨∏ t ∈ T, (ρψ t).1, prod_not_mem T (fun t => (ρψ t).1) 𝔭 (fun t _ => (hρψ t).1), ?_⟩
  intro 𝔮 h𝔮 hr v hv hmem
  haveI := h𝔮
  obtain ⟨t, htT, w, rfl⟩ := hT v
  have ht : pred t := hpred t w hv
  obtain ⟨hψN, hψt⟩ := (hρψ t).2 ht
  have h1 : (1 : B) ⊗ₜ[𝒪] t ∈ N ⊔ (𝔮 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B P)) :=
    one_tmul_mem_sup_of_add hB P N 𝔮 t w hmem
  have h2 : (ρψ t).2 ((1 : B) ⊗ₜ[𝒪] t) ∈ 𝔮 := apply_mem_of_mem_sup _ hψN 𝔮 _ h1
  rw [hψt] at h2
  exact not_mem_of_prod_not_mem T (fun t => (ρψ t).1) 𝔮 hr htT h2

theorem exists_away_edgeNondegAt (hfin : Finite (𝒪 ⧸ Ideal.span {π})) (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) [𝔭.IsPrime] {M' M : FullLattice 𝒪 K}
    (h : d.EdgeNondegAt π 𝔭 M' M) :
    ∃ r : B, r ∉ 𝔭 ∧ ∀ 𝔮 : Ideal B, 𝔮.IsPrime → r ∉ 𝔮 → d.EdgeNondegAt π 𝔮 M' M := by
  obtain ⟨hle, hπM, h1, h2⟩ := h
  haveI := d.invertible M
  haveI := d.invertible M'
  obtain ⟨r₁, hr₁, H₁⟩ := exists_away_of_forall_not_mem hfin hB M (d.line M)
    (fun v : ↥M.1 => (v : Fin 2 → K) ∉ M'.1) (by
      intro t w htw ht
      apply htw
      show ((t : Fin 2 → K) + ((π • w : ↥M.1) : Fin 2 → K)) ∈ M'.1
      refine M'.1.add_mem ht ?_
      rw [Submodule.coe_smul, ← algebraMap_smul K π (w : Fin 2 → K)]
      exact hπM w) 𝔭 h1
  obtain ⟨r₂, hr₂, H₂⟩ := exists_away_of_forall_not_mem hfin hB M' (d.line M')
    (fun v' : ↥M'.1 => ¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K)) (by
      rintro t w htw ⟨w₀, hw₀⟩
      apply htw
      refine ⟨w₀ + ⟨(w : Fin 2 → K), hle w.2⟩, ?_⟩
      show ((t : Fin 2 → K) + ((π • w : ↥M'.1) : Fin 2 → K)) = algebraMap 𝒪 K π • ((w₀ : Fin 2 → K) + (w : Fin 2 → K))
      rw [Submodule.coe_smul, ← algebraMap_smul K π (w : Fin 2 → K), hw₀, smul_add]) 𝔭 h2
  refine ⟨r₁ * r₂, fun hmem => (‹𝔭.IsPrime›.mem_or_mem hmem).elim hr₁ hr₂, ?_⟩
  intro 𝔮 h𝔮 hr
  have hr₁' : r₁ ∉ 𝔮 := fun h' => hr (𝔮.mul_mem_right _ h')
  have hr₂' : r₂ ∉ 𝔮 := fun h' => hr (𝔮.mul_mem_left _ h')
  exact ⟨hle, hπM, H₁ 𝔮 h𝔮 hr₁', H₂ 𝔮 h𝔮 hr₂'⟩

theorem edgeNondegAt_map {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (g : B →ₐ[𝒪] B') (d : DeligneDatum (K := K) π B)
    (𝔮' : Ideal B') [𝔮'.IsPrime] {M' M : FullLattice 𝒪 K} (h : d.EdgeNondegAt π (Ideal.comap g 𝔮') M' M) :
    (d.map π g).EdgeNondegAt π 𝔮' M' M := by
  obtain ⟨hle, hπM, h1, h2⟩ := h
  refine ⟨hle, hπM, fun v hv => ?_, fun v' hv' => ?_⟩
  · rw [← rTensor_one_tmul g M v]
    exact rTensor_not_mem_lineBaseChange_sup g M (d.line M) (d.invertible M) 𝔮' _ (h1 v hv)
  · rw [← rTensor_one_tmul g M' v']
    exact rTensor_not_mem_lineBaseChange_sup g M' (d.line M') (d.invertible M') 𝔮' _ (h2 v' hv')

theorem inEdgeChart_map_of_isUnit (d : DeligneDatum (K := K) π B) (r : B) {M' M : FullLattice 𝒪 K}
    (h : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → r ∉ 𝔮 → d.EdgeNondegAt π 𝔮 M' M)
    {C : Type} [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C) (hr : IsUnit (χ r)) :
    (d.map π χ).InEdgeChart π M' M := by
  intro 𝔮' h𝔮'
  haveI := h𝔮'
  apply edgeNondegAt_map
  refine h _ (Ideal.IsPrime.comap _) ?_
  intro hmem
  rw [Ideal.mem_comap] at hmem
  exact h𝔮'.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hr)

end Openness

section Fibre

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {L : Type} [CommRing L] [Algebra 𝒪 L]

theorem rTensor_mem_lineBaseChange_of_mem_sup (φ : B →ₐ[𝒪] L) (P : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B P)) (x : latticeBaseChange 𝒪 K B P)
    (hx : x ∈ N ⊔ ((RingHom.ker φ) • ⊤ : Submodule B (latticeBaseChange 𝒪 K B P))) :
    LinearMap.rTensor (↥P.1) φ.toLinearMap x ∈ lineBaseChange φ P N := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  have hz0 : LinearMap.rTensor (↥P.1) φ.toLinearMap z = 0 := by
    refine Submodule.smul_induction_on (p := fun z => LinearMap.rTensor (↥P.1) φ.toLinearMap z = 0) hz
      (fun r hr n _ => ?_) (fun a b ha hb => ?_)
    · show LinearMap.rTensor (↥P.1) φ.toLinearMap (r • n) = 0
      rw [rTensor_smul_left, RingHom.mem_ker.mp hr, zero_smul]
    · show LinearMap.rTensor (↥P.1) φ.toLinearMap (a + b) = 0
      rw [map_add, ha, hb, add_zero]
  rw [hz0, add_zero]
  exact Submodule.subset_span ⟨y, hy, rfl⟩

theorem edgeNondegAt_ker_of_map (φ : B →ₐ[𝒪] L) (d : DeligneDatum (K := K) π B) {M' M : FullLattice 𝒪 K}
    (h : (d.map π φ).EdgeNondegAt π ⊥ M' M) : d.EdgeNondegAt π (RingHom.ker φ) M' M := by
  obtain ⟨hle, hπM, h1, h2⟩ := h
  refine ⟨hle, hπM, fun v hv hmem => h1 v hv ?_, fun v' hv' hmem => h2 v' hv' ?_⟩
  · have := rTensor_mem_lineBaseChange_of_mem_sup φ M (d.line M) _ hmem
    rw [rTensor_one_tmul] at this
    exact Submodule.mem_sup_left this
  · have := rTensor_mem_lineBaseChange_of_mem_sup φ M' (d.line M') _ hmem
    rw [rTensor_one_tmul] at this
    exact Submodule.mem_sup_left this

end Fibre

section Generation

variable {R : Type} [CommRing R] {Q : Type} [AddCommGroup Q] [Module R Q]

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

end Generation

section Forms

variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

theorem exists_form_of_generator (N : Submodule R V) [Module.Invertible R (V ⧸ N)] (x : V)
    (hx : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → x ∉ N ⊔ (𝔪 • ⊤ : Submodule R V)) :
    ∃ lam : V →ₗ[R] R, lam x = 1 ∧ LinearMap.ker lam = N := by
  set q : V ⧸ N := N.mkQ x with hq_def
  have hspan : (R ∙ q) = ⊤ := by
    apply eq_top_of_mem_of_forall_not_mem_smul_top _ q (Submodule.mem_span_singleton_self q)
    intro 𝔪 h𝔪 hmem
    exact hx 𝔪 h𝔪 (mem_sup_smul_top_of_mkQ_mem _ _ _ hmem)
  set g : R →ₗ[R] (V ⧸ N) := LinearMap.toSpanSingleton R (V ⧸ N) q with hg_def
  have hsurj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, hg_def, LinearMap.range_toSpanSingleton, hspan]
  have hbij : Function.Bijective g := Module.Invertible.bijective_of_surjective hsurj
  let e : R ≃ₗ[R] (V ⧸ N) := LinearEquiv.ofBijective g hbij
  refine ⟨e.symm.toLinearMap ∘ₗ N.mkQ, ?_, ?_⟩
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq]
    show N.mkQ x = g 1
    rw [hg_def, LinearMap.toSpanSingleton_apply, one_smul]
  · rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

theorem eq_of_le_of_invertible (N N' : Submodule R V) [Module.Invertible R (V ⧸ N)] [Module.Invertible R (V ⧸ N')]
    (hle : N' ≤ N) : N' = N := by
  refine le_antisymm hle ?_
  set g : (V ⧸ N') →ₗ[R] (V ⧸ N) := Submodule.mapQ N' N LinearMap.id hle with hg
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N y
    exact ⟨N'.mkQ x, rfl⟩
  have hinj := (Module.Invertible.bijective_of_surjective hsurj).1
  intro x hx
  have h0 : g (N'.mkQ x) = 0 := by
    show N.mkQ (LinearMap.id x) = 0
    rw [LinearMap.id_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  have : N'.mkQ x = 0 := hinj (by rw [h0, map_zero])
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

theorem fg_of_projective_quotient [Module.Finite R V] (N : Submodule R V) [Module.Projective R (V ⧸ N)] : N.FG := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property N.mkQ (LinearMap.id : (V ⧸ N) →ₗ[R] (V ⧸ N))
    (Submodule.mkQ_surjective N)
  have hN : N = LinearMap.range (LinearMap.id - h ∘ₗ N.mkQ) := by
    apply le_antisymm
    · intro x hx
      refine ⟨x, ?_⟩
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero N).mpr hx, map_zero, sub_zero]
    · rintro _ ⟨x, rfl⟩
      have h0 : N.mkQ ((LinearMap.id - h ∘ₗ N.mkQ : V →ₗ[R] V) x) = 0 := by
        rw [LinearMap.sub_apply, map_sub, LinearMap.id_apply, LinearMap.comp_apply, ← LinearMap.comp_apply N.mkQ h, hh,
          LinearMap.id_apply, sub_self]
      exact (Submodule.Quotient.mk_eq_zero N).mp h0
  rw [hN, LinearMap.range_eq_map]
  exact Submodule.FG.map _ Module.Finite.fg_top

end Forms

section Lattices

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}

def piU (hπ : Irreducible π) : Kˣ := unitOfNeZero (K := K) hπ.ne_zero

theorem piU_coe (hπ : Irreducible π) : ((piU (K := K) hπ : Kˣ) : K) = algebraMap 𝒪 K π := rfl

abbrev piLat (hπ : Irreducible π) (M : FullLattice 𝒪 K) : FullLattice 𝒪 K := FullLattice.act (scalarGL (piU (K := K) hπ)) M

theorem mem_piLat_iff (hπ : Irreducible π) (M : FullLattice 𝒪 K) (v : Fin 2 → K) :
    v ∈ (piLat hπ M).1 ↔ ∃ w ∈ M.1, algebraMap 𝒪 K π • w = v := by
  show v ∈ latticeMap (scalarGL (piU (K := K) hπ)) M.1 ↔ _
  rw [mem_latticeMap_scalarGL, piU_coe]

theorem piLat_le (hπ : Irreducible π) {M' M : FullLattice 𝒪 K} (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    (piLat hπ M).1 ≤ M'.1 := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := (mem_piLat_iff hπ M v).mp hv
  exact hπM w hw

theorem exists_not_smul_mem (hπ : Irreducible π) (M : FullLattice 𝒪 K) :
    ∃ v : ↥M.1, ¬ ∃ w : ↥M.1, (v : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K) := by
  by_contra hcon
  push Not at hcon
  have hle : M.1 ≤ (Ideal.span {π} : Ideal 𝒪) • M.1 := by
    intro v hv
    obtain ⟨w, hw⟩ := hcon ⟨v, hv⟩
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨(w : Fin 2 → K), w.2, ?_⟩
    change (v : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K) at hw
    rw [hw, algebraMap_smul]
  have hjac : (Ideal.span {π} : Ideal 𝒪) ≤ (⊥ : Ideal 𝒪).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit
  have hbot : M.1 = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ M.2.1 hle hjac
  have hspan := M.2.2
  rw [hbot, Submodule.bot_coe, Submodule.span_singleton_eq_bot.mpr rfl] at hspan
  have h1 : (fun _ : Fin 2 => (1 : K)) ∈ (⊤ : Submodule K (Fin 2 → K)) := Submodule.mem_top
  rw [← hspan, Submodule.mem_bot] at h1
  exact one_ne_zero (congrFun h1 0)

variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem exists_form_M (hπ : Irreducible π) (d : DeligneDatum (K := K) π B) {M' M : FullLattice 𝒪 K}
    (hle : M'.1 ≤ M.1) (hd : d.InEdgeChart π M' M) :
    ∃ (lam : latticeBaseChange 𝒪 K B M →ₗ[B] B) (v₀ : ↥M.1), lam ((1 : B) ⊗ₜ[𝒪] v₀) = 1 ∧ LinearMap.ker lam = d.line M := by
  haveI := d.invertible M
  by_cases h : ∃ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1
  · obtain ⟨v, hv⟩ := h
    obtain ⟨lam, h1, h2⟩ := exists_form_of_generator (d.line M) ((1 : B) ⊗ₜ[𝒪] v)
      (fun 𝔪 h𝔪 => (hd 𝔪 h𝔪.isPrime).2.2.1 v hv)
    exact ⟨lam, v, h1, h2⟩
  · push Not at h
    have hMM' : M.1 ≤ M'.1 := fun w hw => h ⟨w, hw⟩
    have heq : M' = M := Subtype.ext (le_antisymm hle hMM')
    subst heq
    obtain ⟨v, hv⟩ := exists_not_smul_mem hπ M'
    obtain ⟨lam, h1, h2⟩ := exists_form_of_generator (d.line M') ((1 : B) ⊗ₜ[𝒪] v)
      (fun 𝔪 h𝔪 => (hd 𝔪 h𝔪.isPrime).2.2.2 v hv)
    exact ⟨lam, v, h1, h2⟩

theorem exists_form_M' (hπ : Irreducible π) (d : DeligneDatum (K := K) π B) {M' M : FullLattice 𝒪 K}
    (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) (hd : d.InEdgeChart π M' M) :
    ∃ (lam' : latticeBaseChange 𝒪 K B M' →ₗ[B] B) (v₀' : ↥M'.1),
      lam' ((1 : B) ⊗ₜ[𝒪] v₀') = 1 ∧ LinearMap.ker lam' = d.line M' := by
  haveI := d.invertible M'
  by_cases h : ∃ v' : ↥M'.1, ¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K)
  · obtain ⟨v', hv'⟩ := h
    obtain ⟨lam', h1, h2⟩ := exists_form_of_generator (d.line M') ((1 : B) ⊗ₜ[𝒪] v')
      (fun 𝔪 h𝔪 => (hd 𝔪 h𝔪.isPrime).2.2.2 v' hv')
    exact ⟨lam', v', h1, h2⟩
  · push Not at h
    obtain ⟨lam, v₀, h1, h2⟩ := exists_form_M hπ d hle hd
    have heq : M' = piLat hπ M := by
      apply Subtype.ext
      apply le_antisymm
      · intro v' hv'
        obtain ⟨w, hw⟩ := h ⟨v', hv'⟩
        exact (mem_piLat_iff hπ M v').mpr ⟨w, w.2, hw.symm⟩
      · exact piLat_le hπ hπM
    subst heq
    set e := actBaseChange B (scalarGL (piU (K := K) hπ)) M with he
    refine ⟨lam ∘ₗ e.symm.toLinearMap, latticeMapEquiv (scalarGL (piU (K := K) hπ)) M.1 v₀, ?_, ?_⟩
    · rw [LinearMap.comp_apply, LinearEquiv.coe_coe]
      have : e.symm ((1 : B) ⊗ₜ[𝒪] latticeMapEquiv (scalarGL (piU (K := K) hπ)) M.1 v₀) = (1 : B) ⊗ₜ[𝒪] v₀ := by
        rw [LinearEquiv.symm_apply_eq, he]; rfl
      rw [this, h1]
    · rw [LinearMap.ker_comp, h2, d.homothety (piU (K := K) hπ) M, ← he]
      exact (Submodule.map_equiv_eq_comap_symm e (d.line M)).symm

end Lattices

section BaseChangeOfForms

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {C : Type} [CommRing C] [Algebra 𝒪 C]

theorem fg_line (d : DeligneDatum (K := K) π B) (P : FullLattice 𝒪 K) : (d.line P).FG := by
  haveI : Module.Finite 𝒪 ↥P.1 := Module.Finite.iff_fg.mpr P.2.1
  haveI : Module.Finite B (latticeBaseChange 𝒪 K B P) := inferInstance
  haveI := d.invertible P
  exact fg_of_projective_quotient (d.line P)

def formBC (χ : B →ₐ[𝒪] C) (P : FullLattice 𝒪 K) (lam : latticeBaseChange 𝒪 K B P →ₗ[B] B) :
    latticeBaseChange 𝒪 K C P →ₗ[C] C :=
  AlgebraTensorModule.lift (LinearMap.toSpanSingleton C (↥P.1 →ₗ[𝒪] C)
    (χ.toLinearMap ∘ₗ (lam.restrictScalars 𝒪 ∘ₗ TensorProduct.mk 𝒪 B (↥P.1) 1)))

theorem formBC_tmul (χ : B →ₐ[𝒪] C) (P : FullLattice 𝒪 K) (lam : latticeBaseChange 𝒪 K B P →ₗ[B] B) (c : C) (m : ↥P.1) :
    formBC χ P lam (c ⊗ₜ[𝒪] m) = c * χ (lam ((1 : B) ⊗ₜ[𝒪] m)) := by
  rw [formBC, AlgebraTensorModule.lift_tmul]
  rfl

theorem formBC_rTensor (χ : B →ₐ[𝒪] C) (P : FullLattice 𝒪 K) (lam : latticeBaseChange 𝒪 K B P →ₗ[B] B)
    (x : latticeBaseChange 𝒪 K B P) :
    formBC χ P lam (LinearMap.rTensor (↥P.1) χ.toLinearMap x) = χ (lam x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul b m =>
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, formBC_tmul, ← map_mul]
    congr 1
    have : (b ⊗ₜ[𝒪] m : latticeBaseChange 𝒪 K B P) = b • ((1 : B) ⊗ₜ[𝒪] m) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul]

theorem sub_smul_mem_lineBaseChange (χ : B →ₐ[𝒪] C) (P : FullLattice 𝒪 K) (lam : latticeBaseChange 𝒪 K B P →ₗ[B] B)
    (v₀ : ↥P.1) (h0 : lam ((1 : B) ⊗ₜ[𝒪] v₀) = 1) (x : latticeBaseChange 𝒪 K C P) :
    x - formBC χ P lam x • ((1 : C) ⊗ₜ[𝒪] v₀) ∈ lineBaseChange χ P (LinearMap.ker lam) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, zero_smul, sub_zero]; exact Submodule.zero_mem _
  | add x y hx hy =>
    have : x + y - formBC χ P lam (x + y) • ((1 : C) ⊗ₜ[𝒪] v₀) =
        (x - formBC χ P lam x • ((1 : C) ⊗ₜ[𝒪] v₀)) + (y - formBC χ P lam y • ((1 : C) ⊗ₜ[𝒪] v₀)) := by
      rw [map_add, add_smul]; abel
    rw [this]
    exact Submodule.add_mem _ hx hy
  | tmul c m =>
    have hker : ((1 : B) ⊗ₜ[𝒪] m - lam ((1 : B) ⊗ₜ[𝒪] m) • ((1 : B) ⊗ₜ[𝒪] v₀) : latticeBaseChange 𝒪 K B P) ∈
        LinearMap.ker lam := by
      rw [LinearMap.mem_ker, map_sub, map_smul, h0, smul_eq_mul, mul_one, sub_self]
    have himg : LinearMap.rTensor (↥P.1) χ.toLinearMap
        ((1 : B) ⊗ₜ[𝒪] m - lam ((1 : B) ⊗ₜ[𝒪] m) • ((1 : B) ⊗ₜ[𝒪] v₀)) ∈ lineBaseChange χ P (LinearMap.ker lam) :=
      Submodule.subset_span ⟨_, hker, rfl⟩
    rw [map_sub, rTensor_smul_left, rTensor_one_tmul, rTensor_one_tmul] at himg
    have heq : c ⊗ₜ[𝒪] m - formBC χ P lam (c ⊗ₜ[𝒪] m) • ((1 : C) ⊗ₜ[𝒪] v₀) =
        c • ((1 : C) ⊗ₜ[𝒪] m - χ (lam ((1 : B) ⊗ₜ[𝒪] m)) • ((1 : C) ⊗ₜ[𝒪] v₀)) := by
      rw [formBC_tmul, smul_sub, ← mul_smul]
      congr 1
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [heq]
    exact Submodule.smul_mem _ _ himg

theorem ker_formBC (χ : B →ₐ[𝒪] C) (P : FullLattice 𝒪 K) (lam : latticeBaseChange 𝒪 K B P →ₗ[B] B)
    (v₀ : ↥P.1) (h0 : lam ((1 : B) ⊗ₜ[𝒪] v₀) = 1) :
    LinearMap.ker (formBC χ P lam) = lineBaseChange χ P (LinearMap.ker lam) := by
  apply le_antisymm
  · intro x hx
    have := sub_smul_mem_lineBaseChange χ P lam v₀ h0 x
    rwa [LinearMap.mem_ker.mp hx, zero_smul, sub_zero] at this
  · rw [lineBaseChange, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, formBC_rTensor, LinearMap.mem_ker.mp hy, map_zero]

theorem apply_eq_zero_of_mem_span (χ : B →ₐ[𝒪] C) (P : FullLattice 𝒪 K) (lam : latticeBaseChange 𝒪 K B P →ₗ[B] B)
    (T : Set (latticeBaseChange 𝒪 K B P)) (hT : ∀ n ∈ T, χ (lam n) = 0)
    (y : latticeBaseChange 𝒪 K B P) (hy : y ∈ Submodule.span B T) : χ (lam y) = 0 := by
  induction hy using Submodule.span_induction with
  | mem n hn => exact hT n hn
  | zero => rw [map_zero, map_zero]
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | smul b a _ ha => rw [map_smul, smul_eq_mul, map_mul, ha, mul_zero]

theorem lineBaseChange_eq_iff (χ : B →ₐ[𝒪] C) (P : FullLattice 𝒪 K) (lam : latticeBaseChange 𝒪 K B P →ₗ[B] B)
    (v₀ : ↥P.1) (h0 : lam ((1 : B) ⊗ₜ[𝒪] v₀) = 1) (N₂ : Submodule B (latticeBaseChange 𝒪 K B P))
    (T : Set (latticeBaseChange 𝒪 K B P)) (hT : Submodule.span B T = N₂)
    [Module.Invertible C (latticeBaseChange 𝒪 K C P ⧸ lineBaseChange χ P (LinearMap.ker lam))]
    [Module.Invertible C (latticeBaseChange 𝒪 K C P ⧸ lineBaseChange χ P N₂)] :
    lineBaseChange χ P N₂ = lineBaseChange χ P (LinearMap.ker lam) ↔ ∀ n ∈ T, χ (lam n) = 0 := by
  constructor
  · intro heq n hn
    have hmem : LinearMap.rTensor (↥P.1) χ.toLinearMap n ∈ lineBaseChange χ P N₂ :=
      Submodule.subset_span ⟨n, by rw [← hT]; exact Submodule.subset_span hn, rfl⟩
    rw [heq, ← ker_formBC χ P lam v₀ h0, LinearMap.mem_ker, formBC_rTensor] at hmem
    exact hmem
  · intro hzero
    apply eq_of_le_of_invertible
    rw [← ker_formBC χ P lam v₀ h0, lineBaseChange, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, formBC_rTensor]
    apply apply_eq_zero_of_mem_span χ P lam T hzero y
    rw [hT]; exact hy

end BaseChangeOfForms

section Assembly

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem isUnit_powers {C : Type} [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C) (f : B) (hf : IsUnit (χ f))
    (y : ↥(Submonoid.powers f)) : IsUnit (χ (y : B)) := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
  rw [← hn, map_pow]
  exact hf.pow n

def liftAway {C : Type} [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C) (f : B) (hf : IsUnit (χ f)) :
    Localization.Away f →ₐ[𝒪] C :=
  IsLocalization.liftAlgHom (M := Submonoid.powers f) (f := χ) (isUnit_powers χ f hf)

theorem liftAway_algebraMap {C : Type} [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C) (f : B) (hf : IsUnit (χ f)) (b : B) :
    liftAway χ f hf (algebraMap B (Localization.Away f) b) = χ b := by
  rw [liftAway, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

theorem liftAway_comp {C : Type} [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C) (f : B) (hf : IsUnit (χ f)) :
    (liftAway χ f hf).comp (IsScalarTower.toAlgHom 𝒪 B (Localization.Away f)) = χ := by
  apply AlgHom.ext
  intro b
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  exact liftAway_algebraMap χ f hf b

theorem map_eq_map_map {C : Type} [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C) (f : B) (hf : IsUnit (χ f))
    (d : DeligneDatum (K := K) π B) :
    d.map π χ = (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away f))).map π (liftAway χ f hf) := by
  have := (Omega K π).map_comp (IsScalarTower.toAlgHom 𝒪 B (Localization.Away f)) (liftAway χ f hf) d
  rw [liftAway_comp] at this
  exact this

theorem exists_num (f : B) (z : Localization.Away f) :
    ∃ (a : B) (n : ℕ), z * algebraMap B (Localization.Away f) f ^ n = algebraMap B (Localization.Away f) a := by
  obtain ⟨⟨a, y⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) z
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
  refine ⟨a, n, ?_⟩
  rw [← map_pow, hn]
  exact h

theorem main (hπ : Irreducible π) (hfin : Finite (𝒪 ⧸ Ideal.span {π})) (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d₁ d₂ : DeligneDatum (K := K) π B)
    {L' : Type} [Field L'] [Algebra 𝒪 L'] (φ : B →ₐ[𝒪] L') (h : d₁.map π φ = d₂.map π φ) :
    ∃ (f : B) (s : Finset B), φ f ≠ 0 ∧
      ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C), IsUnit (χ f) →
        (d₁.map π χ = d₂.map π χ ↔ ∀ b ∈ s, χ b = 0) := by
  classical

  set 𝔭 : Ideal B := RingHom.ker φ with h𝔭
  haveI h𝔭p : 𝔭.IsPrime := RingHom.ker_isPrime φ
  obtain ⟨M', M, hedge⟩ := (d₁.map π φ).exists_edgeNondegAt π (⊥ : Ideal L') Ideal.isPrime_bot
  have hedge₁ : d₁.EdgeNondegAt π 𝔭 M' M := edgeNondegAt_ker_of_map φ d₁ hedge
  have hedge₂ : d₂.EdgeNondegAt π 𝔭 M' M := edgeNondegAt_ker_of_map φ d₂ (by rw [← h]; exact hedge)
  have hle : M'.1 ≤ M.1 := hedge.1
  have hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1 := fun v hv => hedge.2.1 ⟨v, hv⟩

  obtain ⟨r₁, hr₁, H₁⟩ := exists_away_edgeNondegAt hfin hB d₁ 𝔭 hedge₁
  obtain ⟨r₂, hr₂, H₂⟩ := exists_away_edgeNondegAt hfin hB d₂ 𝔭 hedge₂
  set f : B := r₁ * r₂ with hf_def
  have hφf : φ f ≠ 0 := by
    intro h0
    have : f ∈ 𝔭 := by rw [h𝔭, RingHom.mem_ker]; exact h0
    exact (h𝔭p.mem_or_mem this).elim hr₁ hr₂

  set Bf := Localization.Away f with hBf
  set ι : B →ₐ[𝒪] Bf := IsScalarTower.toAlgHom 𝒪 B Bf with hι
  have hιf : IsUnit (ι f) := IsLocalization.Away.algebraMap_isUnit f
  have hι₁ : IsUnit (ι r₁) := isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact hιf)
  have hι₂ : IsUnit (ι r₂) := isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact hιf)
  set D₁ := d₁.map π ι with hD₁
  set D₂ := d₂.map π ι with hD₂
  have hD₁c : D₁.InEdgeChart π M' M := inEdgeChart_map_of_isUnit d₁ r₁ H₁ ι hι₁
  have hD₂c : D₂.InEdgeChart π M' M := inEdgeChart_map_of_isUnit d₂ r₂ H₂ ι hι₂

  obtain ⟨lam, v₀, hlam0, hlamker⟩ := exists_form_M hπ D₁ hle hD₁c
  obtain ⟨lam', v₀', hlam0', hlamker'⟩ := exists_form_M' hπ D₁ hle hπM hD₁c
  obtain ⟨T, hT⟩ := fg_line D₂ M
  obtain ⟨T', hT'⟩ := fg_line D₂ M'

  have hnum : ∀ z : Bf, ∃ a : B, ∃ n : ℕ, z * ι f ^ n = ι a := fun z => exists_num f z
  choose num pw hnum using hnum
  set s : Finset B := (T.image fun n => num (lam n)) ∪ (T'.image fun n' => num (lam' n')) with hs
  refine ⟨f, s, hφf, ?_⟩

  intro C _ _ χ hχf
  set χ' : Bf →ₐ[𝒪] C := liftAway χ f hχf with hχ'
  have hχ'ι : ∀ b : B, χ' (ι b) = χ b := fun b => liftAway_algebraMap χ f hχf b
  have hχ'f : ∀ n : ℕ, IsUnit (χ' (ι f ^ n)) := fun n => by rw [map_pow, hχ'ι]; exact hχf.pow n

  have hval : ∀ z : Bf, χ' z = 0 ↔ χ (num z) = 0 := by
    intro z
    have e := congrArg χ' (hnum z)
    rw [map_mul, hχ'ι] at e
    constructor
    · intro hz; rw [← e, hz, zero_mul]
    · intro hz
      rw [hz] at e
      exact (hχ'f (pw z)).mul_left_eq_zero.mp e

  have hm₁ : d₁.map π χ = D₁.map π χ' := map_eq_map_map χ f hχf d₁
  have hm₂ : d₂.map π χ = D₂.map π χ' := map_eq_map_map χ f hχf d₂

  have hD₁χ : (D₁.map π χ').InEdgeChart π M' M := by
    have := inEdgeChart_map_of_isUnit d₁ r₁ H₁ χ (isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact hχf))
    rwa [hm₁] at this

  haveI i₁ : Module.Invertible C (latticeBaseChange 𝒪 K C M ⧸ lineBaseChange χ' M (LinearMap.ker lam)) := by
    rw [hlamker]; exact (D₁.map π χ').invertible M
  haveI i₂ : Module.Invertible C (latticeBaseChange 𝒪 K C M ⧸ lineBaseChange χ' M (D₂.line M)) :=
    (D₂.map π χ').invertible M
  haveI i₁' : Module.Invertible C (latticeBaseChange 𝒪 K C M' ⧸ lineBaseChange χ' M' (LinearMap.ker lam')) := by
    rw [hlamker']; exact (D₁.map π χ').invertible M'
  haveI i₂' : Module.Invertible C (latticeBaseChange 𝒪 K C M' ⧸ lineBaseChange χ' M' (D₂.line M')) :=
    (D₂.map π χ').invertible M'
  have keyM := lineBaseChange_eq_iff χ' M lam v₀ hlam0 (D₂.line M) (T : Set _) hT
  have keyM' := lineBaseChange_eq_iff χ' M' lam' v₀' hlam0' (D₂.line M') (T' : Set _) hT'
  rw [hm₁, hm₂]
  constructor
  ·
    intro heq b hb
    rw [hs, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hb
    rcases hb with ⟨n, hn, rfl⟩ | ⟨n', hn', rfl⟩
    · rw [← hval]
      refine keyM.mp ?_ n hn
      have := congrArg (fun d : DeligneDatum (K := K) π C => d.line M) heq
      rw [hlamker]
      exact this.symm
    · rw [← hval]
      refine keyM'.mp ?_ n' hn'
      have := congrArg (fun d : DeligneDatum (K := K) π C => d.line M') heq
      rw [hlamker']
      exact this.symm
  ·
    intro hzero
    have hTz : ∀ n ∈ (T : Set _), χ' (lam n) = 0 := fun n hn =>
      (hval _).mpr (hzero _ (by rw [hs, Finset.mem_union, Finset.mem_image]; exact Or.inl ⟨n, hn, rfl⟩))
    have hT'z : ∀ n' ∈ (T' : Set _), χ' (lam' n') = 0 := fun n' hn' =>
      (hval _).mpr (hzero _ (by rw [hs, Finset.mem_union, Finset.mem_image, Finset.mem_image]; exact Or.inr ⟨n', hn', rfl⟩))
    have hM : (D₂.map π χ').line M = (D₁.map π χ').line M := by
      show lineBaseChange χ' M (D₂.line M) = lineBaseChange χ' M (D₁.line M)
      rw [← hlamker]
      exact keyM.mpr hTz
    have hM' : (D₂.map π χ').line M' = (D₁.map π χ').line M' := by
      show lineBaseChange χ' M' (D₂.line M') = lineBaseChange χ' M' (D₁.line M')
      rw [← hlamker']
      exact keyM'.mpr hT'z
    exact (DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ (D₁.map π χ') (D₂.map π χ') M' M hD₁χ hM hM').symm

end Assembly

end P2mKcOmegaDiag

end

open CerednikDrinfeld.FormalOmega LT.LatticeTree in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (hfin : Finite (𝒪 ⧸ Ideal.span {π}))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d₁ d₂ : DeligneDatum (K := K) π B)
    {L' : Type} [Field L'] [Algebra 𝒪 L'] (φ : B →ₐ[𝒪] L') (h : d₁.map π φ = d₂.map π φ) :
    ∃ (f : B) (s : Finset B), φ f ≠ 0 ∧
      ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C), IsUnit (χ f) →
        (d₁.map π χ = d₂.map π χ ↔ ∀ b ∈ s, χ b = 0) :=
  P2mKcOmegaDiag.main hπ hfin hB d₁ d₂ φ h

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finset_forall_map_eq_iff_of_map_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finset_forall_map_eq_iff_of_map_eq (solution)
