-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.form_inP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:44.36271+00:00
-- url     : https://prove2.me/submissions/fa740e46-dbf6-4aa2-b9df-0f0d9dcd8541

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_zero
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_coe_cmb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module Matrix
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
private theorem inP_add {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {a b : K} (ha : InP 𝔭 k a)
    (hb : InP 𝔭 k b) : InP 𝔭 k (a + b) := by
  obtain ⟨s, hs, y, hy, hya⟩ := ha
  obtain ⟨t, ht, z, hz, hzb⟩ := hb
  refine ⟨s * t, fun hst => (‹𝔭.IsPrime›.mem_or_mem hst).elim hs ht, ι t * y + ι s * z,
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hz), ?_⟩
  simp only [map_add, map_mul]
  linear_combination (jK (ι t)) * hya + (jK (ι s)) * hzb
end Formalism.HermitianLattices.Ext.L3.HU
end
end

set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k l : ℕ} {x y : V}
    (hx : x ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V))
    (hy : y ∈ (extP K 𝔭 ^ l • locF 𝔭 (spanO b) : Submodule (𝓞 K) V)) : InP 𝔭 (k + l) (h x y) := by
  have key : ∀ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t = s := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, fun h1 => ‹𝔭.IsPrime›.ne_top ((Ideal.eq_top_iff_one _).2 h1), map_one _⟩
    | mul x x' _ _ hx hx' =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨a', ha', rfl⟩ := hx'
      exact ⟨a * a', fun h1 => (‹𝔭.IsPrime›.mem_or_mem h1).elim ha ha', map_mul _ _ _⟩
  have hc : ∀ w : spanO b, ∃ c : κ → 𝓞 K, cmb b c = w := by
    intro w
    unfold cmb
    exact (Basis.equivFun _).symm.surjective w
  have coords : ∀ u ∈ locF 𝔭 (spanO b),
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c : κ → 𝓞 K, (cmb b c : V) = ι t • u := by
    intro u hu
    have hu' : ∃ s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
        s • u ∈ spanO b := hu
    obtain ⟨s, hs, hsu⟩ := hu'
    obtain ⟨t, ht, rfl⟩ := key s hs
    obtain ⟨c, hcw⟩ := hc ⟨ι t • u, hsu⟩
    exact ⟨t, ht, c, congrArg Subtype.val hcw⟩
  have hfix : ∀ t : 𝓞 F, star (jK (ι t)) = jK (ι t) := fun t => (hF _).2 ⟨(t : F), rfl⟩
  have hst : ∀ r : 𝓞 K, jK (star r) = star (jK r) := fun r => rfl
  have hl : ∀ (r : 𝓞 K) (v w : V), h (r • v) w = star (jK r) * h v w := fun r v w => by
    rw [← algebraMap_smul K r v, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply]
  have hr : ∀ (r : 𝓞 K) (v w : V), h v (r • w) = jK r * h v w := fun r v w => by
    rw [← algebraMap_smul K r w, map_smul, smul_eq_mul]
  have scale : ∀ {m j : ℕ} {c : K} {p : 𝓞 K}, InP 𝔭 m c → p ∈ extP K 𝔭 ^ j →
      InP 𝔭 (m + j) (jK p * c) := by
    intro m j c p hc0 hp
    obtain ⟨t, ht, z, hz, hzc⟩ := hc0
    refine ⟨t, ht, z * p, ?_, ?_⟩
    · rw [pow_add]
      exact Ideal.mul_mem_mul hz hp
    · rw [map_mul, hzc]
      ring
  have mulI : ∀ {m : ℕ} {c : K} (r : 𝓞 K), InP 𝔭 m c → InP 𝔭 m (jK r * c) := by
    intro m c r hc0
    obtain ⟨t, ht, z, hz, hzc⟩ := hc0
    exact ⟨t, ht, r * z, Ideal.mul_mem_left _ r hz, by rw [map_mul, hzc]; ring⟩
  have base : ∀ u ∈ locF 𝔭 (spanO b), ∀ v ∈ locF 𝔭 (spanO b), InP 𝔭 0 (h u v) := by
    intro u hu v hv
    obtain ⟨t, ht, c, hcu⟩ := coords u hu
    obtain ⟨t', ht', c', hcv⟩ := coords v hv
    have e : h (cmb b c : V) (cmb b c' : V) = jK (∑ i, ∑ j, star (c i) * (c' j * H i j)) := by
      rw [coe_cmb, coe_cmb]
      have h1 : ∀ w : V, h (∑ i, c i • b i) w = ∑ i, star (jK (c i)) * h (b i) w := by
        intro w
        rw [map_sum, LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun i _ => hl _ _ _
      rw [h1]
      simp only [map_sum, map_mul, hst, hr, ← hH, Finset.mul_sum]
    rw [hcu, hcv, hl, hr, hfix] at e
    refine ⟨t * t', fun h1 => (‹𝔭.IsPrime›.mem_or_mem h1).elim ht ht', ∑ i, ∑ j, star (c i) * (c' j * H i j), ?_, ?_⟩
    · rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · rw [← e]
      simp only [map_mul]
      ring
  have step1 : ∀ u ∈ locF 𝔭 (spanO b), ∀ {m : ℕ} {w : V},
      w ∈ (extP K 𝔭 ^ m • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) → InP 𝔭 m (h u w) := by
    intro u hu m w hw
    refine Submodule.smul_induction_on (p := fun w => InP 𝔭 m (h u w)) hw
      (fun p hp v hv => ?_) (fun w₁ w₂ h₁ h₂ => ?_)
    · rw [hr]
      have h3 := scale (base u hu v hv) hp
      rwa [zero_add] at h3
    · rw [map_add]
      exact inP_add h₁ h₂
  have hstar : ∀ {j m : ℕ} {c : K}, InP 𝔭 m c → ∀ p ∈ extP K 𝔭 ^ j,
      InP 𝔭 (j + m) (star (jK p) * c) := by
    intro j m c hc0 p hp
    have hp' : p ∈ Submodule.span (𝓞 K) (ι '' ((𝔭 ^ j : Ideal (𝓞 F)) : Set (𝓞 F))) := by
      unfold extP at hp
      rw [← Ideal.map_pow] at hp
      exact hp
    clear hp
    induction hp' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      rw [hfix, add_comm]
      refine scale hc0 ?_
      unfold extP
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ht
    | zero => simpa using InP.zero (𝔭 := 𝔭) (K := K) (j + m)
    | add x y _ _ hx hy =>
      rw [map_add, star_add, add_mul]
      exact inP_add hx hy
    | smul r x _ hx =>
      rw [smul_eq_mul, map_mul, star_mul', mul_assoc, ← hst]
      exact mulI _ hx
  refine Submodule.smul_induction_on (p := fun w => InP 𝔭 (k + l) (h w y)) hx
    (fun p hp u hu => ?_) (fun w₁ w₂ h₁ h₂ => ?_)
  · rw [hl]
    exact hstar (step1 u hu hy) p hp
  · rw [map_add, LinearMap.add_apply]
    exact inP_add h₁ h₂
end Formalism.HermitianLattices.Ext.L3.HU
