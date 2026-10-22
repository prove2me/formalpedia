-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.radial_poly_pos
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T22:37:08.218992+00:00
-- url     : https://prove2.me/submissions/bd6f1093-4e04-4c8e-b67f-4e22f05fe298

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Definitions.Def_BirkhoffGlobalSection_RadialCertificate
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_00
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_01
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_02
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_03
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_04
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_05
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_06
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_07
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_08
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_09
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_10
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_11
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_12
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_13
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_14
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_certC_part_15

namespace BirkhoffGlobalSection.TangentialHessian.Checker.Data

/-- The whole certificate is accepted: assemble the 236 chunk checks from the 16 parts. -/
theorem certC_check : check NP.centredEnc certC = true := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_00
  obtain ⟨h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_01
  obtain ⟨h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_02
  obtain ⟨h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_03
  obtain ⟨h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_04
  obtain ⟨h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_05
  obtain ⟨h90, h91, h92, h93, h94, h95, h96, h97, h98, h99, h100, h101, h102, h103, h104⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_06
  obtain ⟨h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, h119⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_07
  obtain ⟨h120, h121, h122, h123, h124, h125, h126, h127, h128, h129, h130, h131, h132, h133, h134⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_08
  obtain ⟨h135, h136, h137, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_09
  obtain ⟨h150, h151, h152, h153, h154, h155, h156, h157, h158, h159, h160, h161, h162, h163, h164⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_10
  obtain ⟨h165, h166, h167, h168, h169, h170, h171, h172, h173, h174, h175, h176, h177, h178, h179⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_11
  obtain ⟨h180, h181, h182, h183, h184, h185, h186, h187, h188, h189, h190, h191, h192, h193, h194⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_12
  obtain ⟨h195, h196, h197, h198, h199, h200, h201, h202, h203, h204, h205, h206, h207, h208, h209⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_13
  obtain ⟨h210, h211, h212, h213, h214, h215, h216, h217, h218, h219, h220, h221, h222, h223, h224⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_14
  obtain ⟨h225, h226, h227, h228, h229, h230, h231, h232, h233, h234, h235⟩ := BirkhoffGlobalSection.TangentialHessian.certC_part_15
  show checkTree NP.centredEnc certC certC_tree certC_box = true
  simp only [certC_tree, checkTree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90, h91, h92, h93, h94, h95, h96, h97, h98, h99, h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, h119, h120, h121, h122, h123, h124, h125, h126, h127, h128, h129, h130, h131, h132, h133, h134, h135, h136, h137, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149, h150, h151, h152, h153, h154, h155, h156, h157, h158, h159, h160, h161, h162, h163, h164, h165, h166, h167, h168, h169, h170, h171, h172, h173, h174, h175, h176, h177, h178, h179, h180, h181, h182, h183, h184, h185, h186, h187, h188, h189, h190, h191, h192, h193, h194, h195, h196, h197, h198, h199, h200, h201, h202, h203, h204, h205, h206, h207, h208, h209, h210, h211, h212, h213, h214, h215, h216, h217, h218, h219, h220, h221, h222, h223, h224, h225, h226, h227, h228, h229, h230, h231, h232, h233, h234, h235, Bool.and_self]

end BirkhoffGlobalSection.TangentialHessian.Checker.Data

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian in
theorem solution (μ c Z u r : ℝ)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (hZ : 0 ≤ Z) (hz : 2 * Z ≤ (3 - 2 * μ) / 5) (hu1 : u ≤ Z) (hu2 : -Z ≤ u)
    (hr : 0 < r) (hr2 : r ^ 2 = 4 * Z ^ 2 - 4 * u + 1) (hR : 0 ≤ radrR2 μ c Z u r) :
    0 < radEr3 μ Z u r ∧ 0 < radFr6 μ c Z u r := by
  -- the certificate `certC` (numerics/phase3/cert_C_tree_dyadic.json), checked by the kernel
  have hZ3 : Z ≤ 3 / 10 := by linarith
  have hflat : ∀ (n : ℕ) (p : Checker.Poly Checker.Dy) (x : List ℝ), x.length = n →
      Checker.NP.DPoly.eval (⟨n, Checker.NP.ofFlat n p⟩ : Checker.NP.DPoly Checker.Dy) x =
        Checker.evalR p x := fun n p x h => Checker.NP.eval_ofFlat n p x h
  have hx : Checker.InBox [μ, c, Z, u] Checker.Data.certC.box := by
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
      (List.Forall₂.cons ?_ List.Forall₂.nil))) <;>
    · unfold Checker.Mem; simp only [Checker.Dy.cnum_toReal_mk]
      constructor <;> norm_num <;> linarith
  have hr2' : r ^ 2 = Checker.NP.DPoly.eval Checker.Data.certC.rSq [μ, c, Z, u] := by
    show r ^ 2 = Checker.NP.DPoly.eval ⟨4, Checker.NP.ofFlat 4 Checker.Data.certC_rSq⟩ _
    rw [hflat 4 _ _ rfl, hr2]
    simp [Checker.Data.certC_rSq, Checker.evalR, Checker.monoR]; ring
  have hhyp : ∀ p ∈ Checker.Data.certC.hyps,
      0 ≤ Checker.NP.DPoly.eval p ([μ, c, Z, u] ++ [r]) := by
    intro p hp
    simp only [Checker.Data.certC, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [hflat 5 q _ rfl]
    simp only [Checker.Data.certC_hyps, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · simp [Checker.evalR, Checker.monoR]; linarith
    · simp [Checker.evalR, Checker.monoR]; linarith
    · simp [Checker.evalR, Checker.monoR]; linarith
    · refine le_of_le_of_eq hR ?_
      simp [Checker.evalR, Checker.monoR]; unfold radrR2; ring
  have hg := Checker.check_sound Checker.NP.centredEnc_sound Checker.Data.certC
    Checker.Data.certC_check _ hx r hr hr2' hhyp
  have hE := hg _ (List.mem_map_of_mem List.mem_cons_self)
  have hF := hg _ (List.mem_map_of_mem (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [hflat 5 _ _ rfl] at hE hF
  constructor
  · convert hE using 1; simp [Checker.evalR, Checker.monoR]; unfold radEr3; ring
  · convert hF using 1; simp [Checker.evalR, Checker.monoR]; unfold radFr6 radEr3 radrR2; ring
