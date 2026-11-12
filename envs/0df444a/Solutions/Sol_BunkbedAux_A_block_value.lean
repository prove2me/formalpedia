-- Prove2me | solution 1 for BunkbedAux.A_block_value
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T03:00:10.014239+00:00
-- url     : https://prove2.me/submissions/e4b812fe-257c-4c37-aecc-34d0efe8936a

import Theorems.Thm_BunkbedAux_alt_block_sum
import Definitions.Def_BunkbedWZSurgery
open Bunkbed Bunkbed.Hyper Bunkbed.Hyper.WZExt Finset SimpleGraph

private lemma fin2_cases : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide

private def ofSig (σ : Fin 6 → Fin 2) : Fin 6 → WZExt :=
  fun h => if σ h = 0 then Sum.inr 1 else Sum.inr 3

private def toSig (Ψ : Fin 6 → WZExt) : Fin 6 → Fin 2 :=
  fun h => if Ψ h = Sum.inr 1 then 0 else 1

private lemma cfg_ofSig (σ : Fin 6 → Fin 2) :
    wzOfExt (ofSig σ) = fun p => if p.2 = σ p.1 then WZ.abc else WZ.a_b_c := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [wzOfExt, ofSig]
  rcases fin2_cases (σ i) with h | h <;> fin_cases j <;> simp [h, toPair]

private lemma wt_ofSig (P : WZ → ℚ) (σ : Fin 6 → Fin 2) :
    (∏ h, wt P (ofSig σ h)) = (P .abc * P .a_b_c - P .ab_c * P .ac_b) ^ 6 := by
  rw [Finset.prod_congr rfl (fun h _ =>
    show wt P (ofSig σ h) = P .abc * P .a_b_c - P .ab_c * P .ac_b by
      simp only [ofSig]; split <;> simp [wt])]
  simp [Finset.prod_const]

theorem solution (P : WZ → ℚ) :
    ∑ Ψ ∈ univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ ({Sum.inr 1, Sum.inr 3} : Finset WZExt)),
        (∏ h, wt P (Ψ h)) *
          ((if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) then (1 : ℚ) else 0)
          - (if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) then (1 : ℚ) else 0))
      = (P .abc * P .a_b_c - P .ab_c * P .ac_b) ^ 6 := by
  have hbij : ∑ Ψ ∈ univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ ({Sum.inr 1, Sum.inr 3} : Finset WZExt)),
        (∏ h, wt P (Ψ h)) *
          ((if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) then (1 : ℚ) else 0)
          - (if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) then (1 : ℚ) else 0))
      = ∑ σ : Fin 6 → Fin 2, (P .abc * P .a_b_c - P .ab_c * P .ac_b) ^ 6 *
          ((if (wzGraph hollomTriple hollomT
                (fun p => if p.2 = σ p.1 then WZ.abc else WZ.a_b_c)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) then (1 : ℚ) else 0)
          - (if (wzGraph hollomTriple hollomT
                (fun p => if p.2 = σ p.1 then WZ.abc else WZ.a_b_c)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) then (1 : ℚ) else 0)) := by
    refine Finset.sum_nbij' toSig ofSig ?_ ?_ ?_ ?_ ?_
    · intro Ψ _; exact Finset.mem_univ _
    · intro σ _
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => ?_⟩
      simp only [ofSig]; split <;> simp
    · intro Ψ hΨ
      have hmem := (Finset.mem_filter.mp hΨ).2
      funext h
      rcases Finset.mem_insert.mp (hmem h) with h1 | h1
      · simp [ofSig, toSig, h1]
      · simp [ofSig, toSig, Finset.mem_singleton.mp h1]
    · intro σ _; funext h; simp only [ofSig, toSig]
      rcases fin2_cases (σ h) with h1 | h1 <;> simp_all
    · intro Ψ hΨ
      have hmem := (Finset.mem_filter.mp hΨ).2
      have hoe : ofSig (toSig Ψ) = Ψ := by
        funext h
        rcases Finset.mem_insert.mp (hmem h) with h1 | h1
        · simp [ofSig, toSig, h1]
        · simp [ofSig, toSig, Finset.mem_singleton.mp h1]
      have hcfg : wzOfExt Ψ = fun p => if p.2 = toSig Ψ p.1 then WZ.abc else WZ.a_b_c := by
        conv_lhs => rw [← hoe]
        exact cfg_ofSig (toSig Ψ)
      have hwt : (∏ h, wt P (Ψ h))
          = (P WZ.abc * P WZ.a_b_c - P WZ.ab_c * P WZ.ac_b) ^ 6 := by
        conv_lhs => rw [← hoe]
        exact wt_ofSig P (toSig Ψ)
      rw [hcfg, hwt]
  rw [hbij, ← Finset.mul_sum, BunkbedAux.alt_block_sum, mul_one]
