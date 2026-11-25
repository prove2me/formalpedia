-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.cocycleLiftOfExact_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:40:01.844513+00:00
-- url     : https://prove2.me/submissions/6ce8610d-2bfa-4fc0-901b-9c73376df0fc

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_DiffOneSmulOfTower
import Theorems.Thm_Formalism_CoboundaryTransfers_chase_qpow_bij
import Theorems.Thm_Formalism_CoboundaryTransfers_chase_Q_sub
import Theorems.Thm_Formalism_CoboundaryTransfers_chase_Q_smul
import Theorems.Thm_Formalism_CoboundaryTransfers_chase_Q_smulA
import Theorems.Thm_Formalism_CoboundaryTransfers_chase_Q_N
import Theorems.Thm_P2M_Formalism_CoboundaryTransfers_chase_Q___f9ab1d245c0a
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_d1_smul
import Theorems.Thm_Formalism_CoboundaryTransfers_diffOne_sub
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_d1_phi_sub_gamma_sub_eq_zero
import Theorems.Thm_Formalism_CoboundaryTransfers_map_diffOne
import Theorems.Thm_Formalism_CoboundaryTransfers_chase_hom_Q
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.CoboundaryTransfers
section DiagramChase₂
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {D' : Type} [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
end DiagramChase₂
private lemma exists_phi_X_eq_X_mul {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) :
    ∃ v, B.φ B.X = B.X * v := by
  cases B
  assumption
end Formalism.CoboundaryTransfers
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
namespace Formalism.CoboundaryTransfers
theorem _root_.solution : DiagramChase₂ := by
  unfold DiagramChase₂
  intro O A _ _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S e c hC hR hT
  unfold CokerKilled at hC
  unfold RatSurj at hR
  unfold WachMod.TorsKilled at hT
  unfold Lifts

  have hpφ : ∀ t, S.π.f (W₁.φ t) = W₂.φ (S.π.f t) := by
    generalize S.π = g
    cases g
    assumption
  have hpγ : ∀ t, S.π.f (W₁.γ t) = W₂.γ (S.π.f t) := by
    generalize S.π = g
    cases g
    assumption
  have hiN : ∀ t ∈ W₀.N, S.ι.f t ∈ W₁.N := by
    generalize S.ι = g
    cases g
    assumption
  have hpO : ∀ (r : O) (t : D₁), S.π.f (r • t) = r • S.π.f t := by
    intro r t
    first
    | exact LinearMap.map_smul_of_tower _ r t
    | rw [algebra_compatible_smul A r t, map_smul, ← algebra_compatible_smul A r]
  have hiO : ∀ (r : O) (t : D₀), S.ι.f (r • t) = r • S.ι.f t := by
    intro r t
    first
    | exact LinearMap.map_smul_of_tower _ r t
    | rw [algebra_compatible_smul A r t, map_smul, ← algebra_compatible_smul A r]

  have key : ∀ (w : D₀) (t : D₁), S.ι.f w = B.X • t → ∃ t₀, S.ι.f t₀ = t ∧ w = B.X • t₀ := by
    intro w t h
    have h0 : S.π.f t = 0 := by
      apply W₂.X_inj
      rw [← map_smul, ← h]
      exact (S.exact _).2 ⟨w, rfl⟩
    obtain ⟨t₀, ht₀⟩ := (S.exact t).1 h0
    refine ⟨t₀, ht₀, S.ι_inj ?_⟩
    rw [map_smul, ht₀, h]
  have qsat : ∀ w : D₀, W₁.QInv (S.ι.f w) → W₀.QInv w := by
    intro w h
    show B.Q ^ M • w ∈ W₀.N
    apply S.sat
    rw [map_smul]
    exact h
  intro y z hyz
  obtain ⟨k, y₁, z₁, hc₁, x, hx, hpy₁, hpz₁⟩ := hR y z hyz
  obtain ⟨⟨hQy, n, hn, rfl⟩, hd⟩ := hyz
  obtain ⟨⟨hQy₁, n₁, hn₁, hz₁⟩, hd₁⟩ := hc₁

  obtain ⟨a, ha, hpa⟩ := hC (B.Q ^ M • y) hQy
  obtain ⟨yt, hyt⟩ : ∃ t, B.Q ^ M • t = a := (chase_qpow_bij W₁ M).2 a
  have hQyt : W₁.QInv yt := by
    show B.Q ^ M • yt ∈ W₁.N
    rw [hyt]
    exact ha
  have hpyt : S.π.f yt = ((B.p : O) ^ e) • y := by
    apply (chase_qpow_bij W₂ M).1
    show B.Q ^ M • S.π.f yt = B.Q ^ M • (((B.p : O) ^ e) • y)
    rw [← map_smul S.π.f, hyt, hpa, smul_comm (B.Q ^ M) ((B.p : O) ^ e) y]
  obtain ⟨b, hb, hpb⟩ := hC n hn
  have hpzt : S.π.f (B.X • b) = ((B.p : O) ^ e) • (B.X • n) := by
    rw [map_smul, hpb, smul_comm B.X ((B.p : O) ^ e) n]
  have hω₁ : S.π.f (W₁.d1 yt (B.X • b)) = 0 := by
    rw [map_diffOne, hpyt, hpzt, WachMod_d1_smul, hd, smul_zero]
  obtain ⟨ω, hω⟩ := (S.exact _).1 hω₁

  obtain ⟨y', hQy', hγyt⟩ := W₁.γ_QN yt hQyt
  obtain ⟨v, hv⟩ := exists_phi_X_eq_X_mul B
  have hiω : S.ι.f ω = B.X • (y' - (v • W₁.φ b - b)) := by
    rw [hω, WachMod.d1, hγyt, W₁.φ_smul, hv, mul_smul, smul_sub, smul_sub]
  have hsmem : W₁.QInv (y' - (v • W₁.φ b - b)) :=
    chase_Q_sub W₁ hQy' (chase_Q_sub W₁ (chase_Q_smulA W₁ v (chase_Q_φ W₁ hb)) (chase_Q_N W₁ hb))
  obtain ⟨s₀, hs₀, hωs₀⟩ := key ω _ hiω
  have hC2 : W₀.C2 ω := ⟨s₀, qsat s₀ (by rw [hs₀]; exact hsmem), hωs₀⟩

  obtain ⟨m, hm, hpm⟩ := hC x hx
  have hpu : S.π.f (((B.p : O) ^ e) • y₁ - (W₁.φ m - m)) = ((B.p : O) ^ k) • (((B.p : O) ^ e) • y) := by
    rw [map_sub, map_sub, hpO, hpφ, hpy₁, hpm, map_smul W₂.φ, smul_add, smul_sub, smul_comm ((B.p : O) ^ e) ((B.p : O) ^ k) y]
    abel
  have hpv : S.π.f (((B.p : O) ^ e) • z₁ - (W₁.γ m - m)) = ((B.p : O) ^ k) • (((B.p : O) ^ e) • (B.X • n)) := by
    rw [map_sub, map_sub, hpO, hpγ, hpz₁, hpm, map_smul W₂.γ, smul_add, smul_sub, smul_comm ((B.p : O) ^ e) ((B.p : O) ^ k) (B.X • n)]
    abel
  have hα0 : S.π.f (((B.p : O) ^ k) • yt - (((B.p : O) ^ e) • y₁ - (W₁.φ m - m))) = 0 := by
    rw [map_sub, hpO, hpyt, hpu, sub_self]
  have hβ0 : S.π.f (((B.p : O) ^ k) • (B.X • b) - (((B.p : O) ^ e) • z₁ - (W₁.γ m - m))) = 0 := by
    rw [map_sub, hpO, hpzt, hpv, sub_self]
  obtain ⟨α, hα⟩ := (S.exact _).1 hα0
  obtain ⟨β, hβ⟩ := (S.exact _).1 hβ0
  have hduv : W₁.d1 (((B.p : O) ^ e) • y₁ - (W₁.φ m - m)) (((B.p : O) ^ e) • z₁ - (W₁.γ m - m)) = 0 := by
    rw [diffOne_sub, WachMod_d1_smul, hd₁, smul_zero, WachMod_d1_phi_sub_gamma_sub_eq_zero, sub_zero]
  have hdαβ : W₀.d1 α β = ((B.p : O) ^ k) • ω := by
    apply S.ι_inj
    rw [map_diffOne, hα, hβ, diffOne_sub, hduv, sub_zero, WachMod_d1_smul, ← hω, hiO]
  have hQu : W₁.QInv (((B.p : O) ^ e) • y₁ - (W₁.φ m - m)) :=
    chase_Q_sub W₁ (chase_Q_smul W₁ _ hQy₁) (chase_Q_sub W₁ (chase_Q_φ W₁ hm) (chase_Q_N W₁ hm))
  have hQα : W₀.QInv α := qsat α (by rw [hα]; exact chase_Q_sub W₁ (chase_Q_smul W₁ _ hQyt) hQu)
  obtain ⟨m', hm', hγm⟩ := W₁.γ_N m hm
  have hiβ : S.ι.f β = B.X • (((B.p : O) ^ k) • b - (((B.p : O) ^ e) • n₁ - m')) := by
    rw [hβ, hz₁, hγm, smul_sub, smul_sub, smul_comm B.X ((B.p : O) ^ k) b, smul_comm B.X ((B.p : O) ^ e) n₁]
  have hKb : ((B.p : O) ^ k) • b - (((B.p : O) ^ e) • n₁ - m') ∈ W₁.N :=
    W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hb) (W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hn₁) hm')
  obtain ⟨β₀, hβ₀, hββ₀⟩ := key β _ hiβ
  have hcob : W₀.IsCob2 (((B.p : O) ^ k) • ω) :=
    ⟨α, β, ⟨hQα, β₀, S.sat β₀ (by rw [hβ₀]; exact hKb), hββ₀⟩, hdαβ.symm⟩

  obtain ⟨α', β', ⟨hQα', n', hn', hβ'⟩, hcω⟩ := hT ω hC2 ⟨k, hcob⟩
  refine ⟨c • yt - S.ι.f α', c • (B.X • b) - S.ι.f β', ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact chase_Q_sub W₁ (chase_Q_smul W₁ c hQyt) (chase_hom_Q S.ι hQα')
  · refine ⟨c • b - S.ι.f n', W₁.N.sub_mem (W₁.N.smul_of_tower_mem c hb) (hiN n' hn'), ?_⟩
    rw [hβ', map_smul, smul_sub, smul_comm B.X c b]
  · rw [diffOne_sub, WachMod_d1_smul, ← map_diffOne S.ι α' β', ← hcω, ← hω, hiO, sub_self]
  · rw [map_sub, hpO, hpyt, (S.exact _).2 ⟨α', rfl⟩, sub_zero, mul_comm, mul_smul]
  · rw [map_sub, hpO, hpzt, (S.exact _).2 ⟨β', rfl⟩, sub_zero, mul_comm, mul_smul]
end Formalism.CoboundaryTransfers
