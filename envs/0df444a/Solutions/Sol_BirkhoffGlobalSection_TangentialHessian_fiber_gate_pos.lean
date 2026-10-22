-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.fiber_gate_pos
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T23:04:50.683675+00:00
-- url     : https://prove2.me/submissions/fd7fc17f-ccc9-4120-81b0-5a20323557c2

import Definitions.Def_BirkhoffGlobalSection_FiberGateCertificate
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_00
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_01
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_02
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_03
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_04
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_05
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_06
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_07
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_08
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_09
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_10
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_11
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_12
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_13
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_14
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_15
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_16
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_17
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_18
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_19
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_20
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_21
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_22
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_23
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_24
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_25
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_26
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_27
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_28
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_29
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_30
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_31
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_32
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_33
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_gateCert_part_34

namespace BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.GateTM BirkhoffGlobalSection.TangentialHessian.Checker.GateAsm

/-- The whole certificate is accepted: assemble the 365 chunk checks from the 35 parts. -/
theorem gt_check : check GQ.enc (gateCert gt_tree) = true := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_00
  obtain ⟨h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_01
  obtain ⟨h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_02
  obtain ⟨h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_03
  obtain ⟨h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_04
  obtain ⟨h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_05
  obtain ⟨h67, h68, h69, h70, h71, h72, h73, h74, h75⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_06
  obtain ⟨h76, h77, h78, h79, h80, h81, h82, h83, h84⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_07
  obtain ⟨h85, h86, h87, h88, h89, h90, h91, h92, h93⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_08
  obtain ⟨h94, h95, h96, h97, h98, h99, h100, h101, h102, h103⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_09
  obtain ⟨h104, h105, h106, h107, h108, h109, h110, h111, h112⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_10
  obtain ⟨h113, h114, h115, h116, h117, h118, h119, h120, h121⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_11
  obtain ⟨h122, h123, h124, h125, h126, h127, h128, h129, h130, h131⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_12
  obtain ⟨h132, h133, h134, h135, h136, h137, h138, h139, h140⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_13
  obtain ⟨h141, h142, h143, h144, h145, h146, h147, h148, h149, h150⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_14
  obtain ⟨h151, h152, h153, h154, h155, h156, h157, h158, h159⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_15
  obtain ⟨h160, h161, h162, h163, h164, h165, h166, h167, h168, h169, h170⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_16
  obtain ⟨h171, h172, h173, h174, h175, h176, h177, h178, h179, h180⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_17
  obtain ⟨h181, h182, h183, h184, h185, h186, h187, h188, h189, h190, h191, h192⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_18
  obtain ⟨h193, h194, h195, h196, h197, h198, h199, h200, h201, h202, h203, h204⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_19
  obtain ⟨h205, h206, h207, h208, h209, h210, h211, h212, h213⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_20
  obtain ⟨h214, h215, h216, h217, h218, h219, h220, h221, h222, h223⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_21
  obtain ⟨h224, h225, h226, h227, h228, h229, h230, h231⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_22
  obtain ⟨h232, h233, h234, h235, h236, h237, h238, h239, h240, h241, h242⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_23
  obtain ⟨h243, h244, h245, h246, h247, h248, h249, h250, h251, h252, h253, h254⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_24
  obtain ⟨h255, h256, h257, h258, h259, h260, h261, h262, h263, h264, h265, h266, h267⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_25
  obtain ⟨h268, h269, h270, h271, h272, h273, h274, h275, h276, h277, h278, h279, h280, h281, h282, h283, h284⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_26
  obtain ⟨h285, h286, h287, h288, h289, h290, h291, h292, h293, h294, h295⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_27
  obtain ⟨h296, h297, h298, h299, h300, h301, h302, h303⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_28
  obtain ⟨h304, h305, h306, h307, h308, h309, h310, h311, h312, h313⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_29
  obtain ⟨h314, h315, h316, h317, h318, h319, h320, h321, h322⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_30
  obtain ⟨h323, h324, h325, h326, h327, h328, h329, h330, h331, h332, h333, h334, h335⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_31
  obtain ⟨h336, h337, h338, h339, h340, h341, h342, h343, h344, h345, h346, h347⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_32
  obtain ⟨h348, h349, h350, h351, h352, h353, h354, h355, h356, h357, h358, h359⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_33
  obtain ⟨h360, h361, h362, h363, h364⟩ := BirkhoffGlobalSection.TangentialHessian.gateCert_part_34
  show checkTree GQ.enc (gateCert gt_tree) gt_tree rootBox = true
  generalize gateCert gt_tree = C at *
  simp only [gt_tree, checkTree, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90, h91, h92, h93, h94, h95, h96, h97, h98, h99, h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, h119, h120, h121, h122, h123, h124, h125, h126, h127, h128, h129, h130, h131, h132, h133, h134, h135, h136, h137, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149, h150, h151, h152, h153, h154, h155, h156, h157, h158, h159, h160, h161, h162, h163, h164, h165, h166, h167, h168, h169, h170, h171, h172, h173, h174, h175, h176, h177, h178, h179, h180, h181, h182, h183, h184, h185, h186, h187, h188, h189, h190, h191, h192, h193, h194, h195, h196, h197, h198, h199, h200, h201, h202, h203, h204, h205, h206, h207, h208, h209, h210, h211, h212, h213, h214, h215, h216, h217, h218, h219, h220, h221, h222, h223, h224, h225, h226, h227, h228, h229, h230, h231, h232, h233, h234, h235, h236, h237, h238, h239, h240, h241, h242, h243, h244, h245, h246, h247, h248, h249, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, h261, h262, h263, h264, h265, h266, h267, h268, h269, h270, h271, h272, h273, h274, h275, h276, h277, h278, h279, h280, h281, h282, h283, h284, h285, h286, h287, h288, h289, h290, h291, h292, h293, h294, h295, h296, h297, h298, h299, h300, h301, h302, h303, h304, h305, h306, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h317, h318, h319, h320, h321, h322, h323, h324, h325, h326, h327, h328, h329, h330, h331, h332, h333, h334, h335, h336, h337, h338, h339, h340, h341, h342, h343, h344, h345, h346, h347, h348, h349, h350, h351, h352, h353, h354, h355, h356, h357, h358, h359, h360, h361, h362, h363, h364, Bool.and_self]

end BirkhoffGlobalSection.TangentialHessian.Checker.GateCertData

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian in
theorem solution (μ c r : ℝ) (s : Phase)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (hr : 0 < r) (hr2 : r ^ 2 = secondCollisionDistanceSq s)
    (hz : 2 * zNormSq s ≤ (3 - 2 * μ) / 5) (_hF : 0 ≤ fibF μ c r s) :
    0 < fibG μ c r s ∧
      fibF μ c r s * (fibBeta1 μ c r s ^ 2 + fibBeta2 μ c r s ^ 2) < fibG μ c r s ^ 2 :=
  Checker.GateAsm.fiber_gate_pos_of_check Checker.GateCertData.gt_check μ c r s hμ0 hμhalf hc0 hc1 hr hr2 hz
